/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (c) 2013-2015 Regents of the University of California.
 *
 * This file is part of ndn-cxx library (NDN C++ library with eXperimental eXtensions).
 *
 * ndn-cxx library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later version.
 *
 * ndn-cxx library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.
 *
 * You should have received copies of the GNU General Public License and GNU Lesser
 * General Public License along with ndn-cxx, e.g., in COPYING.md file.  If not, see
 * <http://www.gnu.org/licenses/>.
 *
 * See AUTHORS.md for complete list of ndn-cxx authors and contributors.
 */

#include "interest.hpp"
#include "util/random.hpp"
#include "util/crypto.hpp"
#include "data.hpp"
#include "ns3/Signer.hpp"

using namespace ns3;

namespace ndn {

BOOST_CONCEPT_ASSERT((boost::EqualityComparable<Interest>));
BOOST_CONCEPT_ASSERT((WireEncodable<Interest>));
BOOST_CONCEPT_ASSERT((WireEncodableWithEncodingBuffer<Interest>));
BOOST_CONCEPT_ASSERT((WireDecodable<Interest>));
static_assert(std::is_base_of<tlv::Error, Interest::Error>::value,
              "Interest::Error must inherit from tlv::Error");

Interest::Interest()
  : m_interestLifetime(time::milliseconds::min())
  , m_selectedDelegationIndex(INVALID_SELECTED_DELEGATION_INDEX)
  , m_type(default_)
  , m_signature(NULL)
  //, m_size (0)
{
  m_bloomFilters.clear();
  m_signerList.clear();
}


Interest::Interest(const Name& name)
  : m_name(name)
  , m_interestLifetime(time::milliseconds::min())
  , m_selectedDelegationIndex(INVALID_SELECTED_DELEGATION_INDEX)
  , m_type(default_)
  , m_signature(NULL)
{
}

Interest::Interest(const Name& name, const time::milliseconds& interestLifetime)
  : m_name(name)
  , m_interestLifetime(interestLifetime)
  , m_selectedDelegationIndex(INVALID_SELECTED_DELEGATION_INDEX)
  , m_type(default_)
  , m_signature(NULL)
  //, m_size (0)
{
  m_bloomFilters.clear();
  m_signerList.clear();
}

Interest::Interest(const Block& wire)
{
  wireDecode(wire);
}

uint32_t
Interest::getNonce() const
{
  if (!m_nonce.hasWire())
    const_cast<Interest*>(this)->setNonce(random::generateWord32());

  if (m_nonce.value_size() == sizeof(uint32_t))
    return *reinterpret_cast<const uint32_t*>(m_nonce.value());
  else {
    // for compatibility reasons.  Should be removed eventually
    return readNonNegativeInteger(m_nonce);
  }
}

Interest&
Interest::setNonce(uint32_t nonce)
{
  if (m_wire.hasWire() && m_nonce.value_size() == sizeof(uint32_t)) {
    std::memcpy(const_cast<uint8_t*>(m_nonce.value()), &nonce, sizeof(nonce));
  }
  else {
    m_nonce = makeBinaryBlock(tlv::Nonce,
                              reinterpret_cast<const uint8_t*>(&nonce),
                              sizeof(nonce));
    m_wire.reset();
  }
  return *this;
}

void
Interest::refreshNonce()
{
  if (!hasNonce())
    return;

  uint32_t oldNonce = getNonce();
  uint32_t newNonce = oldNonce;
  while (newNonce == oldNonce)
    newNonce = random::generateWord32();

  setNonce(newNonce);
}

bool
Interest::matchesName(const Name& name) const
{
  if (name.size() < m_name.size())
    return false;

  if (!m_name.isPrefixOf(name))
    return false;

  if (getMinSuffixComponents() >= 0 &&
      // name must include implicit digest
      !(name.size() - m_name.size() >= static_cast<size_t>(getMinSuffixComponents())))
    return false;

  if (getMaxSuffixComponents() >= 0 &&
      // name must include implicit digest
      !(name.size() - m_name.size() <= static_cast<size_t>(getMaxSuffixComponents())))
    return false;

  if (!getExclude().empty() &&
      name.size() > m_name.size() &&
      getExclude().isExcluded(name[m_name.size()]))
    return false;

  return true;
}

bool
Interest::matchesData(const Data& data) const
{
  size_t interestNameLength = m_name.size();
  const Name& dataName = data.getName();
  size_t fullNameLength = dataName.size() + 1;

  // check MinSuffixComponents
  bool hasMinSuffixComponents = getMinSuffixComponents() >= 0;
  size_t minSuffixComponents = hasMinSuffixComponents ?
                               static_cast<size_t>(getMinSuffixComponents()) : 0;
  if (!(interestNameLength + minSuffixComponents <= fullNameLength))
    return false;

  // check MaxSuffixComponents
  bool hasMaxSuffixComponents = getMaxSuffixComponents() >= 0;
  if (hasMaxSuffixComponents &&
      !(interestNameLength + getMaxSuffixComponents() >= fullNameLength))
    return false;

  // check prefix
  if (interestNameLength == fullNameLength) {
    if (m_name.get(-1).isImplicitSha256Digest()) {
      if (m_name != data.getFullName())
        return false;
    }
    else {
      // Interest Name is same length as Data full Name, but last component isn't digest
      // so there's no possibility of matching
      return false;
    }
  }
  else {
    // Interest Name is a strict prefix of Data full Name
    if (!m_name.isPrefixOf(dataName))
      return false;
  }

  // check Exclude
  // Exclude won't be violated if Interest Name is same as Data full Name
  if (!getExclude().empty() && fullNameLength > interestNameLength) {
    if (interestNameLength == fullNameLength - 1) {
      // component to exclude is the digest
      if (getExclude().isExcluded(data.getFullName().get(interestNameLength)))
        return false;
      // There's opportunity to inspect the Exclude filter and determine whether
      // the digest would make a difference.
      // eg. "<NameComponent>AA</NameComponent><Any/>" doesn't exclude any digest -
      //     fullName not needed;
      //     "<Any/><NameComponent>AA</NameComponent>" and
      //     "<Any/><ImplicitSha256DigestComponent>ffffffffffffffffffffffffffffffff
      //      </ImplicitSha256DigestComponent>"
      //     excludes all digests - fullName not needed;
      //     "<Any/><ImplicitSha256DigestComponent>80000000000000000000000000000000
      //      </ImplicitSha256DigestComponent>"
      //     excludes some digests - fullName required
      // But Interests that contain the exact Data Name before digest and also
      // contain Exclude filter is too rare to optimize for, so we request
      // fullName no mater what's in the Exclude filter.
    }
    else {
      // component to exclude is not the digest
      if (getExclude().isExcluded(dataName.get(interestNameLength)))
        return false;
    }
  }

  // check PublisherPublicKeyLocator
  const KeyLocator& publisherPublicKeyLocator = this->getPublisherPublicKeyLocator();
  if (!publisherPublicKeyLocator.empty()) {
    const Signature& signature = data.getSignature();
    const Block& signatureInfo = signature.getInfo();
    Block::element_const_iterator it = signatureInfo.find(tlv::KeyLocator);
    if (it == signatureInfo.elements_end()) {
      return false;
    }
    if (publisherPublicKeyLocator.wireEncode() != *it) {
      return false;
    }
  }

  return true;
}

template<encoding::Tag TAG>
size_t
Interest::wireEncode(EncodingImpl<TAG>& encoder) const
{
  size_t totalLength = 0;

  // Interest ::= INTEREST-TYPE TLV-LENGTH
  //                Name
  //                Selectors?
  //                Nonce
  //                InterestLifetime?
  //                Link?
  //                SelectedDelegation?

  // (reverse encoding)

  if (hasLink()) {
    if (hasSelectedDelegation()) {
      totalLength += prependNonNegativeIntegerBlock(encoder,
                                                    tlv::SelectedDelegation,
                                                    m_selectedDelegationIndex);
    }
    totalLength += encoder.prependBlock(m_link);
  }
  else {
    BOOST_ASSERT(!hasSelectedDelegation());
  }

  // InterestLifetime
  if (getInterestLifetime() >= time::milliseconds::zero() &&
      getInterestLifetime() != DEFAULT_INTEREST_LIFETIME)
    {
      totalLength += prependNonNegativeIntegerBlock(encoder,
                                                    tlv::InterestLifetime,
                                                    getInterestLifetime().count());
    }

  // Nonce
  getNonce(); // to ensure that Nonce is properly set
  totalLength += encoder.prependBlock(m_nonce);

  bool hasBls = m_signature != NULL;
  if(hasBls) {
    { // serialize bf vector
      vector<byte> serializedContainers;
      serializedContainers.clear();

      unsigned char* charptr;
      // serialize bf vector size
      size_t vectorSize = m_bloomFilters.size();
      charptr = (unsigned char*)&vectorSize;
      for (int i = 0; i < size_tBytes; i++) {
        serializedContainers.push_back(*(charptr + i));
      }
      // serialize vector
      int counter = 0;
      for (size_t i = 0; i < vectorSize; i++) {
        BloomFilterContainer* container = m_bloomFilters[i];
        unsigned char buffer[container->getByteSize()];
        container->serialize(buffer, container->getByteSize());
        for (size_t j = 0; j < container->getByteSize(); j++) {
          serializedContainers.push_back(*(buffer + j));
        }
        counter++;
        counter+=container->getReductions().size();
      }
      // if (m_type == InterestType::CAR)
      //   std::cout << "serialized " << getName().toUri() << " with " << counter << " BFs \n";      
      
      // preppend the vector
      byte containerBuffer[serializedContainers.size()];
      copy(serializedContainers.begin(), serializedContainers.end(), containerBuffer);
      totalLength += prependByteArrayBlock(encoder, tlv::BfContainerVector, containerBuffer, serializedContainers.size());
    }

    { // serialize signer List
      unsigned char* charptr;
      vector<byte> serializedSigners;
      serializedSigners.clear();
      // serialize vector size
      size_t vectorSize = m_signerList.size();
      charptr = (unsigned char*)&vectorSize;
      for (int i = 0; i < size_tBytes; i++) {
        serializedSigners.push_back(*(charptr + i));
      }
      // serialize vector
      for (size_t i = 0; i < vectorSize; i++) {
        SidPkPair* pair = m_signerList[i];
        unsigned char buffer[pair->getByteSize()];
        pair->serialize(buffer, pair->getByteSize());
        if (!pair->m_pk->on_curve())
          cout << "serialization: pk not on curve \n";

        for (size_t j = 0; j < pair->getByteSize(); j++) {
          serializedSigners.push_back(*(buffer + j));
        }
      }
      // preppend the vector
      byte signerBuffer[serializedSigners.size()];
      copy(serializedSigners.begin(), serializedSigners.end(), signerBuffer);
      totalLength += prependByteArrayBlock(encoder, tlv::SignerList, signerBuffer, serializedSigners.size());
    }

    { // serialize signature
      byte sigser[96];
      m_signature->serialize(sigser);
      totalLength += prependByteArrayBlock(encoder, tlv::Signature, sigser, 96);
      if (!m_signature->on_curve())
        cout << "serialization: signature not on curve \n";
    }
  }
  
  totalLength += prependNonNegativeIntegerBlock(encoder, tlv::HasBls, (uint64_t)hasBls);

  { // serialize interest type
    totalLength += prependNonNegativeIntegerBlock(encoder, tlv::InterestType, (uint64_t)m_type);
  }

  // Selectors
  if (hasSelectors())
    {
      totalLength += getSelectors().wireEncode(encoder);
    }

  // Name
  totalLength += getName().wireEncode(encoder);

  totalLength += encoder.prependVarNumber(totalLength);
  totalLength += encoder.prependVarNumber(tlv::Interest);
  return totalLength;
}

template size_t
Interest::wireEncode<encoding::EncoderTag>(EncodingImpl<encoding::EncoderTag>& encoder) const;

template size_t
Interest::wireEncode<encoding::EstimatorTag>(EncodingImpl<encoding::EstimatorTag>& encoder) const;

const Block&
Interest::wireEncode() const
{
  if (m_wire.hasWire())
    return m_wire;

  EncodingEstimator estimator;
  size_t estimatedSize = wireEncode(estimator);

  EncodingBuffer buffer(estimatedSize, 0);
  wireEncode(buffer);

  // to ensure that Nonce block points to the right memory location
  const_cast<Interest*>(this)->wireDecode(buffer.block());

  return m_wire;
}

void
Interest::wireDecode(const Block& wire)
{
  m_wire = wire;
  m_wire.parse();

// Interest ::= INTEREST-TYPE TLV-LENGTH
    //                Name
    //                Selectors?
    //                BLS signatures
    //                    type
    //                    signature
    //                    signer list
    //                    bf container list
    //                Nonce
    //                InterestLifetime?
    //                Link?
    //                SelectedDelegation?

  if (m_wire.type() != tlv::Interest)
    BOOST_THROW_EXCEPTION(Error("Unexpected TLV number when decoding Interest"));

  // Name
  m_name.wireDecode(m_wire.get(tlv::Name));

  // Selectors
  Block::element_const_iterator val = m_wire.find(tlv::Selectors);
  if (val != m_wire.elements_end())
    {
      m_selectors.wireDecode(*val);
    }
  else
    m_selectors = Selectors();

  val = m_wire.find(tlv::InterestType);
  if (val != m_wire.elements_end())
  {
    m_type = (InterestType)readNonNegativeInteger(*val);
  }

  bool hasBls = false;
  
  val = m_wire.find(tlv::HasBls);
  if (val != m_wire.elements_end())
  {
    hasBls = (bool)readNonNegativeInteger(*val);
  }

  if (hasBls) {
    //NDN_LOG_UNCOND("found bls");
    val = m_wire.find(tlv::Signature);
    if (val != m_wire.elements_end())
    {
      byte array[96];
      std::memcpy(array, val->value(), val->value_size());
      m_signature = new P1_Affine(&array[0]);

      if (!m_signature->on_curve())
        cout << "deserialization: singature not on curve \n";
    }

    val = m_wire.find(tlv::SignerList);
    if (val != m_wire.elements_end())
    {
      byte array[val->value_size()];
      std::memcpy(array, val->value(), val->value_size());
      unsigned char* data = &array[0];
      size_t vectorSize = *((size_t*)data);
      data += size_tBytes;

      for (size_t i = 0; i < vectorSize; i++) {
        SidPkPair* pair = new SidPkPair();
        pair->deserialize(data);
        m_signerList.push_back(pair);
        if (!pair->m_pk->on_curve())
          cout << "deserialization: public key not on curve";
        data += pair->getByteSize();
      }
    }

    val = m_wire.find(tlv::BfContainerVector);
    if (val != m_wire.elements_end())
    {
      byte array[val->value_size()];
      std::memcpy(array, val->value(), val->value_size());
      unsigned char* data = &array[0];
      size_t vectorSize = *((size_t*)data);
      data += size_tBytes;
      int counter = 0;
      for (size_t i = 0; i < vectorSize; i++) {
        BloomFilterContainer* container = new BloomFilterContainer();
        container->deserialize(data);
        data += container->getByteSize();
        m_bloomFilters.push_back(container);

        counter++;
        counter+= container->getReductions().size();
      }
      // if (m_type == InterestType::CAR)
      //   std::cout << "deserialized " << getName().toUri() << " with " << counter << " BFs \n";
    }
  }

  // Nonce
  m_nonce = m_wire.get(tlv::Nonce);

  // InterestLifetime
  val = m_wire.find(tlv::InterestLifetime);
  if (val != m_wire.elements_end())
    {
      m_interestLifetime = time::milliseconds(readNonNegativeInteger(*val));
    }
  else
    {
      m_interestLifetime = DEFAULT_INTEREST_LIFETIME;
    }

  // Link object
  val = m_wire.find(tlv::Data);
  if (val != m_wire.elements_end())
    {
      m_link = (*val);
    }

  // SelectedDelegation
  val = m_wire.find(tlv::SelectedDelegation);
  if (val != m_wire.elements_end()) {
    if (!this->hasLink()) {
      BOOST_THROW_EXCEPTION(Error("Interest contains selectedDelegation, but no LINK object"));
    }
    uint64_t selectedDelegation = readNonNegativeInteger(*val);
    if (selectedDelegation < uint64_t(Link::countDelegationsFromWire(m_link))) {
      m_selectedDelegationIndex = static_cast<size_t>(selectedDelegation);
    }
    else {
      BOOST_THROW_EXCEPTION(Error("Invalid selected delegation index when decoding Interest"));
    }
  }
}

bool
Interest::hasLink() const
{
  if (m_link.hasWire())
    return true;
  return false;
}

Link
Interest::getLink() const
{
  if (hasLink())
    {
      return Link(m_link);
    }
  BOOST_THROW_EXCEPTION(Error("There is no encapsulated link object"));
}

void
Interest::setLink(const Block& link)
{
  m_link = link;
  if (!link.hasWire()) {
    BOOST_THROW_EXCEPTION(Error("The given link does not have a wire format"));
  }
  m_wire.reset();
  this->unsetSelectedDelegation();
}

void
Interest::unsetLink()
{
  m_link.reset();
  m_wire.reset();
  this->unsetSelectedDelegation();
}

bool
Interest::hasSelectedDelegation() const
{
  if (m_selectedDelegationIndex != INVALID_SELECTED_DELEGATION_INDEX)
    {
      return true;
    }
  return false;
}

Name
Interest::getSelectedDelegation() const
{
  if (!hasSelectedDelegation()) {
    BOOST_THROW_EXCEPTION(Error("There is no encapsulated selected delegation"));
  }
  return std::get<1>(Link::getDelegationFromWire(m_link, m_selectedDelegationIndex));
}

void
Interest::setSelectedDelegation(const Name& delegationName)
{
  size_t delegationIndex = Link::findDelegationFromWire(m_link, delegationName);
  if (delegationIndex != INVALID_SELECTED_DELEGATION_INDEX) {
    m_selectedDelegationIndex = delegationIndex;
  }
  else {
    BOOST_THROW_EXCEPTION(std::invalid_argument("Invalid selected delegation name"));
  }
  m_wire.reset();
}

void
Interest::setSelectedDelegation(size_t delegationIndex)
{
  if (delegationIndex >= Link(m_link).getDelegations().size()) {
    BOOST_THROW_EXCEPTION(Error("Invalid selected delegation index"));
  }
  m_selectedDelegationIndex = delegationIndex;
  m_wire.reset();
}

void
Interest::unsetSelectedDelegation()
{
  m_selectedDelegationIndex = INVALID_SELECTED_DELEGATION_INDEX;
  m_wire.reset();
}

std::ostream&
operator<<(std::ostream& os, const Interest& interest)
{
  os << interest.getName();

  char delim = '?';

  if (interest.getMinSuffixComponents() >= 0) {
    os << delim << "ndn.MinSuffixComponents=" << interest.getMinSuffixComponents();
    delim = '&';
  }
  if (interest.getMaxSuffixComponents() >= 0) {
    os << delim << "ndn.MaxSuffixComponents=" << interest.getMaxSuffixComponents();
    delim = '&';
  }
  if (interest.getChildSelector() >= 0) {
    os << delim << "ndn.ChildSelector=" << interest.getChildSelector();
    delim = '&';
  }
  if (interest.getMustBeFresh()) {
    os << delim << "ndn.MustBeFresh=" << interest.getMustBeFresh();
    delim = '&';
  }
  if (interest.getInterestLifetime() >= time::milliseconds::zero()
      && interest.getInterestLifetime() != DEFAULT_INTEREST_LIFETIME) {
    os << delim << "ndn.InterestLifetime=" << interest.getInterestLifetime().count();
    delim = '&';
  }

  if (interest.hasNonce()) {
    os << delim << "ndn.Nonce=" << interest.getNonce();
    delim = '&';
  }
  if (!interest.getExclude().empty()) {
    os << delim << "ndn.Exclude=" << interest.getExclude();
    delim = '&';
  }

  return os;
}
  #pragma region BLS_implementation
 // BLS signature methods implementation
  std::string Interest::getTypeString()
  {
    switch (m_type)
    {
    case Interest::CAR:
      return "CAR";
    case Interest::CA:
      return "CA";
    case Interest::content:
      return "content";
    default:
      break;
    }
    return "";
  }

  std::vector<BloomFilterContainer*> Interest::getBloomFilters()
  {
    return m_bloomFilters;
  }

  P1_Affine* Interest::getSignature()
  {
    return m_signature;
  }

  void Interest::addBloomFilter(BloomFilterContainer* bf)
  {
    m_bloomFilters.push_back(bf);
  }

  vector<BloomFilterContainer*> Interest::getAllBloomFilters()
  {
    vector<BloomFilterContainer* > result;

    for (size_t i = 0; i < m_bloomFilters.size(); i++) {
      BloomFilterContainer *current = m_bloomFilters[i];
      result.push_back(new BloomFilterContainer(current->getSignerId(), *(current->getBloomFilter())));
      vector<BloomFilterContainer *> tempBfs = current->reconstructBfs();
      result.insert(result.end(), tempBfs.begin(), tempBfs.end());
    }

    return result;
  }

  std::vector<SidPkPair*> Interest::getSignerList()
  {
    return m_signerList;
  }

  Interest::InterestType Interest::getInterestType() const
  {
    return m_type;
  }

  void Interest::setInterestType(const Interest::InterestType& type)
  {
    m_type = type;
  }

  void Interest::setSignature(blst::P1_Affine *signature) 
  {
    m_signature = signature;
  }

  /**
   * @brief adds a new SidPkPair into the signer list avoiding adding duplicates based on SignerId
   *
   * @param signerPair
   */
  void Interest::addSigner(SidPkPair* signerPair)
  {
    for (size_t i = 0; i < m_signerList.size(); i++) {
      if (signerPair->m_signerId == m_signerList[i]->m_signerId) {
        if (!signerPair->m_pk->is_equal(*(m_signerList[i]->m_pk))) {
          printf("ERROR: signerId %lu has colliding public keys \n", m_signerList[i]->m_signerId);
          P2_Affine *pk = m_signerList[i]->m_pk;
          byte pkBuffer[192];
          pk->serialize(pkBuffer);
          cout << "Printing pk for signer " << m_signerList[i]->m_signerId << "\n";
          for (size_t j=0; j < 192; j++) {
            cout << (uint8_t) pkBuffer[j] << " ";
          }
          cout << " vs \n";
          pk = signerPair->m_pk;
          pk->serialize(pkBuffer);
          for (size_t j=0; j < 192; j++) {
            cout << (uint8_t) pkBuffer[j] << " ";
          }
          cout << "\n";

          return;
        }
      }
    }
    m_signerList.push_back(signerPair);
  }

  void Interest::mergeBf(BloomFilterContainer* bloomFilter)
  {
    //printf("mergeBf: entered method \n");
    if (m_bloomFilters.size() == 0)
    {
      m_bloomFilters.push_back(bloomFilter);
      return;
    }
    // find the closest bloomFilter
    unsigned long minDistance = -1;
    BloomFilterContainer* closestBloomFilter;
    size_t index = 0;
    //printf("mergeBf: size of m_bloomFilters %lu \n", m_bloomFilters.size());
    for (size_t i = 0; i < m_bloomFilters.size(); i++) {
      if (bloomFilter == m_bloomFilters[i])
      {
        printf("You cannot merge a BF container with itself \n");
        continue;
      }
      unsigned long distance = m_bloomFilters[i]->calculateDistance(bloomFilter->getBloomFilter());
      if (minDistance == (unsigned long)-1 || distance < minDistance) {       
        minDistance = distance;
        closestBloomFilter = m_bloomFilters[i];
        index = i;
      }
    }
    if (minDistance == (unsigned long)-1) {
      m_bloomFilters.push_back(bloomFilter);
    }
    //printf("mergeBf: finished finding nearest \n");
    if (minDistance <= (unsigned long)DELTA_MAX) {
      // printf("merfing with distance %lu \n", minDistance);
      if (closestBloomFilter->merge(bloomFilter)) {
        return;
      }
      else if (bloomFilter->merge(closestBloomFilter)) {
        m_bloomFilters[index] = bloomFilter;
      }
      else {
        m_bloomFilters.push_back(bloomFilter);
      }
    }
    else {
      // this could be added after this for loop to not slow down next iteration
      // printf("Could not reduce bf, the distance is too great: %lu \n", minDistance);
      m_bloomFilters.push_back(bloomFilter);
    }
  }

  void Interest::merge(Interest* other)
  {
    if (m_type != other->getInterestType()) {
      printf("not merging, wrong type \n");
      return;
    }

    if (other->getBloomFilters().size() == 0) {
      printf("not merging, no bloom filters \n");
      return;
    }

    // this is probably not necessary, received interests are already verified
    
    // if (!other->verify(additionalSignerList)) {
    //   printf("could not verify Interest being merged \n");
    //   return;
    // }

    for (size_t i = 0; i < other->getBloomFilters().size(); i++) {
      mergeBf(other->getBloomFilters()[i]);
    }
    // merge the signer lists
    for (size_t i = 0; i < other->getSignerList().size(); i++) {
      addSigner(other->getSignerList()[i]);
    }

    P1 temp = P1(*m_signature);
    temp.aggregate(*other->getSignature());
    m_signature = new P1_Affine(temp);
  }

  bool Interest::verify2(vector<SidPkPair*> additionalSignerList)
  {
    if (m_signature == NULL) {
      printf("ERROR: no signature present");
      return false;
    }

    std::vector<SignedMessage> messages;
    messages.clear();
    std::vector<P1_Affine> signatures;
    signatures.clear();
    signatures.push_back(*m_signature);

    std::vector<BloomFilterContainer*> bfs = getAllBloomFilters();
    for (size_t i = 0; i < bfs.size(); i++)
    {
      size_t index = getPublicKeyIndex(bfs[i]->getSignerId());

      if (index == (size_t)-1) {
        printf("did not find public key of a main container, id: %lu \n", bfs[i]->getSignerId());
        return false;
      }
      if (index == (size_t)-1) {
        index = searchForPk(bfs[i]->getSignerId(), additionalSignerList);
      }
      if (index == (size_t)-1) {
        printf("did not find public key of a main container, id: %lu \n", bfs[i]->getSignerId());
        return false;
      }
      messages.push_back(SignedMessage(bfs[i]->getBloomFilter(), m_signerList[index]->m_pk));
    }

    return Signer::verify(messages, signatures);
  }


  bool Interest::verify(vector<SidPkPair*> additionalSignerList)
  {
    if (m_signature == NULL) {
      printf("ERROR: no signature present");
      return false;
    }    
    std::vector<SignedMessage> messages;
    messages.clear();

    BloomFilterContainer* bfContainer;
    BloomFilterContainer* reduction;

    for (size_t i = 0; i < m_bloomFilters.size(); i++) {
      bfContainer = m_bloomFilters[i];
      size_t index = getPublicKeyIndex(bfContainer->getSignerId());

      if (index == (size_t)-1) {
        printf("did not find public key of a main container, id: %lu \n", bfContainer->getSignerId());
        return false;
      }
      messages.push_back(SignedMessage(bfContainer->getBloomFilter(), m_signerList[index]->m_pk));

      std::vector<BloomFilterContainer*> reconstructed = bfContainer->reconstructBfs();
      for (size_t j = 0; j < reconstructed.size(); j++) {
        reduction = reconstructed[j];
        size_t reductionIndex = getPublicKeyIndex(reduction->getSignerId());
        if (reductionIndex == (size_t)-1) {
          reductionIndex = searchForPk(reduction->getSignerId(), additionalSignerList);
        }
        if (reductionIndex == (size_t)-1) {
          printf("did not find public key of a reduction for SignerId %lu \n", reduction->getSignerId());
          return false;
        }
        messages.push_back(SignedMessage(reduction->getBloomFilter(), m_signerList[reductionIndex]->m_pk));
      }
    }
    //printf("at the verification: got %lu signed messages for %lu total BFs \n", messages.size(), getAllBloomFilters().size());
    return Signer::verify(messages, m_signature);
  }

  bool Interest::verify3(vector<SidPkPair*> onlySignerList)
  {
    if (m_signature == NULL) {
      printf("ERROR: no signature present");
      return false;
    }

    std::vector<SignedMessage> messages;
    messages.clear();

    std::vector<BloomFilterContainer*> bfs = getAllBloomFilters();
    for (size_t i = 0; i < bfs.size(); i++)
    {
      size_t index = searchForPk(bfs[i]->getSignerId(), onlySignerList);
      
      if (index == (size_t)-1) {
        printf("did not find public key of a main container, id: %lu \n", bfs[i]->getSignerId());
        return false;
      }
      messages.push_back(SignedMessage(bfs[i]->getBloomFilter(), onlySignerList[index]->m_pk));
    }

    return Signer::verify(messages, m_signature);
  }

  // extend this when you have a public key cache
  size_t Interest::getPublicKeyIndex(SignerId signerId)
  {
    return searchForPk(signerId, m_signerList);
  }

  size_t Interest::searchForPk(SignerId signerId, vector<SidPkPair*> list)
  {
    for (size_t i = 0; i < list.size(); i++) {
      //printf("index %lu, signer id %lu \n", i, m_signerList[i]->m_signerId);
      if (list[i]->m_signerId == signerId) return i;
    }
    return -1;
  }

  size_t Interest::estimateByteSize(bool log)
  {
    size_t reductionCount = 0;
    size_t size = 0;
    for (size_t i = 0; i < m_bloomFilters.size(); i++)
    {
      if (log)
        printf("Estimating byte size: adding %lu \n", m_bloomFilters[i]->getByteSize());
      size += m_bloomFilters[i]->getByteSize();
      reductionCount += m_bloomFilters[i]->getReductions().size();
    }
    if (log)
      printf("Estimating byte size: have %lu bf containers and %lu reductions \n", m_bloomFilters.size(), reductionCount);

    size += m_signerList.size() * 192; // for the signer list
    size += 96; // for the signature
    size += 100; // other stuff

    return size;
  }

  void Interest::logDebug()
  {
    cout << "Interest debug: " << getName().toUri() << "\n";
    m_bloomFilters[0]->printFilter();
    for (size_t i = 0; i < m_signerList.size(); i++) {
      P2_Affine *pk = m_signerList[i]->m_pk;
      byte pkBuffer[192];
      pk->serialize(pkBuffer);
      cout << "Printing pk for signer " << m_signerList[i]->m_signerId << "\n";
      for (size_t j=0; j < 192; j++) {
        cout << (uint8_t) pkBuffer[j] << "  ";
      }
      cout << "\n";
    }
    byte sBuffer[96];
    m_signature->serialize(sBuffer);
    cout << "Printing signature " << "\n";
    for (size_t j=0; j < 96; j++) {
      cout << (uint8_t) sBuffer[j] << "  ";
    }
    cout << "\n";
  }

  void Interest::logDebugContent()
  {
    cout << "Interest debug: " << getName().toUri() << "\n";
    for (size_t i = 0; i < m_bloomFilters.size(); i++) {
      
      BloomFilterContainer* container = m_bloomFilters[i];
      container->printFilter();
      for (size_t j = 0; j < container->getReductions().size(); j++) {
        container->getReductions()[j]->printIndexVector();
      }
    }
    cout << "\n";
  }

  #pragma endregion
} // namespace ndn
