-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice09_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice09_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:18:29.494866+00:00
-- url     : https://prove2.me/theorems/ae5a2a96-b309-46cf-8b2a-e97ef3011edc
-- title:
--   Exact Pell certificate records 577–640
-- statement:
--   The exact consecutive certificate records 577 through 640 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_010

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice09_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨5655,pellFiniteCertificate_5655⟩,
   ⟨5663,pellFiniteCertificate_5663⟩,
   ⟨5671,pellFiniteCertificate_5671⟩,
   ⟨5695,pellFiniteCertificate_5695⟩,
   ⟨5703,pellFiniteCertificate_5703⟩,
   ⟨5711,pellFiniteCertificate_5711⟩,
   ⟨5719,pellFiniteCertificate_5719⟩,
   ⟨5727,pellFiniteCertificate_5727⟩,
   ⟨5735,pellFiniteCertificate_5735⟩,
   ⟨5743,pellFiniteCertificate_5743⟩,
   ⟨5759,pellFiniteCertificate_5759⟩,
   ⟨5767,pellFiniteCertificate_5767⟩,
   ⟨5783,pellFiniteCertificate_5783⟩,
   ⟨5791,pellFiniteCertificate_5791⟩,
   ⟨5799,pellFiniteCertificate_5799⟩,
   ⟨5807,pellFiniteCertificate_5807⟩,
   ⟨5815,pellFiniteCertificate_5815⟩,
   ⟨5839,pellFiniteCertificate_5839⟩,
   ⟨5847,pellFiniteCertificate_5847⟩,
   ⟨5855,pellFiniteCertificate_5855⟩,
   ⟨5863,pellFiniteCertificate_5863⟩,
   ⟨5871,pellFiniteCertificate_5871⟩,
   ⟨5879,pellFiniteCertificate_5879⟩,
   ⟨5903,pellFiniteCertificate_5903⟩,
   ⟨5911,pellFiniteCertificate_5911⟩,
   ⟨5919,pellFiniteCertificate_5919⟩,
   ⟨5927,pellFiniteCertificate_5927⟩,
   ⟨5935,pellFiniteCertificate_5935⟩,
   ⟨5943,pellFiniteCertificate_5943⟩,
   ⟨5951,pellFiniteCertificate_5951⟩,
   ⟨5959,pellFiniteCertificate_5959⟩,
   ⟨5983,pellFiniteCertificate_5983⟩,
   ⟨5991,pellFiniteCertificate_5991⟩,
   ⟨5999,pellFiniteCertificate_5999⟩,
   ⟨6007,pellFiniteCertificate_6007⟩,
   ⟨6015,pellFiniteCertificate_6015⟩,
   ⟨6023,pellFiniteCertificate_6023⟩,
   ⟨6031,pellFiniteCertificate_6031⟩,
   ⟨6047,pellFiniteCertificate_6047⟩,
   ⟨6055,pellFiniteCertificate_6055⟩,
   ⟨6063,pellFiniteCertificate_6063⟩,
   ⟨6071,pellFiniteCertificate_6071⟩,
   ⟨6079,pellFiniteCertificate_6079⟩,
   ⟨6087,pellFiniteCertificate_6087⟩,
   ⟨6095,pellFiniteCertificate_6095⟩,
   ⟨6103,pellFiniteCertificate_6103⟩,
   ⟨6119,pellFiniteCertificate_6119⟩,
   ⟨6127,pellFiniteCertificate_6127⟩,
   ⟨6135,pellFiniteCertificate_6135⟩,
   ⟨6143,pellFiniteCertificate_6143⟩,
   ⟨6151,pellFiniteCertificate_6151⟩,
   ⟨6159,pellFiniteCertificate_6159⟩,
   ⟨6167,pellFiniteCertificate_6167⟩,
   ⟨6191,pellFiniteCertificate_6191⟩,
   ⟨6199,pellFiniteCertificate_6199⟩,
   ⟨6207,pellFiniteCertificate_6207⟩,
   ⟨6215,pellFiniteCertificate_6215⟩,
   ⟨6231,pellFiniteCertificate_6231⟩,
   ⟨6239,pellFiniteCertificate_6239⟩,
   ⟨6247,pellFiniteCertificate_6247⟩,
   ⟨6263,pellFiniteCertificate_6263⟩,
   ⟨6271,pellFiniteCertificate_6271⟩,
   ⟨6279,pellFiniteCertificate_6279⟩,
   ⟨6287,pellFiniteCertificate_6287⟩]

end D1Bound5


