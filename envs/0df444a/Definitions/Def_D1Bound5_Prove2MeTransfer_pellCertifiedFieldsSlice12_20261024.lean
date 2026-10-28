-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice12_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice12_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:16:55.951737+00:00
-- url     : https://prove2.me/theorems/8c3dfb4f-108f-4f24-9ca5-0337eace4a73
-- title:
--   Exact Pell certificate records 769–832
-- statement:
--   The exact consecutive certificate records 769 through 832 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_013

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice12_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨7543,pellFiniteCertificate_7543⟩,
   ⟨7559,pellFiniteCertificate_7559⟩,
   ⟨7567,pellFiniteCertificate_7567⟩,
   ⟨7583,pellFiniteCertificate_7583⟩,
   ⟨7591,pellFiniteCertificate_7591⟩,
   ⟨7599,pellFiniteCertificate_7599⟩,
   ⟨7607,pellFiniteCertificate_7607⟩,
   ⟨7615,pellFiniteCertificate_7615⟩,
   ⟨7631,pellFiniteCertificate_7631⟩,
   ⟨7639,pellFiniteCertificate_7639⟩,
   ⟨7647,pellFiniteCertificate_7647⟩,
   ⟨7655,pellFiniteCertificate_7655⟩,
   ⟨7663,pellFiniteCertificate_7663⟩,
   ⟨7671,pellFiniteCertificate_7671⟩,
   ⟨7679,pellFiniteCertificate_7679⟩,
   ⟨7687,pellFiniteCertificate_7687⟩,
   ⟨7703,pellFiniteCertificate_7703⟩,
   ⟨7711,pellFiniteCertificate_7711⟩,
   ⟨7719,pellFiniteCertificate_7719⟩,
   ⟨7727,pellFiniteCertificate_7727⟩,
   ⟨7735,pellFiniteCertificate_7735⟩,
   ⟨7743,pellFiniteCertificate_7743⟩,
   ⟨7751,pellFiniteCertificate_7751⟩,
   ⟨7759,pellFiniteCertificate_7759⟩,
   ⟨7783,pellFiniteCertificate_7783⟩,
   ⟨7799,pellFiniteCertificate_7799⟩,
   ⟨7807,pellFiniteCertificate_7807⟩,
   ⟨7815,pellFiniteCertificate_7815⟩,
   ⟨7823,pellFiniteCertificate_7823⟩,
   ⟨7831,pellFiniteCertificate_7831⟩,
   ⟨7847,pellFiniteCertificate_7847⟩,
   ⟨7855,pellFiniteCertificate_7855⟩,
   ⟨7863,pellFiniteCertificate_7863⟩,
   ⟨7871,pellFiniteCertificate_7871⟩,
   ⟨7879,pellFiniteCertificate_7879⟩,
   ⟨7887,pellFiniteCertificate_7887⟩,
   ⟨7895,pellFiniteCertificate_7895⟩,
   ⟨7903,pellFiniteCertificate_7903⟩,
   ⟨7919,pellFiniteCertificate_7919⟩,
   ⟨7927,pellFiniteCertificate_7927⟩,
   ⟨7951,pellFiniteCertificate_7951⟩,
   ⟨7959,pellFiniteCertificate_7959⟩,
   ⟨7967,pellFiniteCertificate_7967⟩,
   ⟨7991,pellFiniteCertificate_7991⟩,
   ⟨7999,pellFiniteCertificate_7999⟩,
   ⟨8007,pellFiniteCertificate_8007⟩,
   ⟨8015,pellFiniteCertificate_8015⟩,
   ⟨8023,pellFiniteCertificate_8023⟩,
   ⟨8031,pellFiniteCertificate_8031⟩,
   ⟨8039,pellFiniteCertificate_8039⟩,
   ⟨8047,pellFiniteCertificate_8047⟩,
   ⟨8063,pellFiniteCertificate_8063⟩,
   ⟨8071,pellFiniteCertificate_8071⟩,
   ⟨8079,pellFiniteCertificate_8079⟩,
   ⟨8087,pellFiniteCertificate_8087⟩,
   ⟨8095,pellFiniteCertificate_8095⟩,
   ⟨8103,pellFiniteCertificate_8103⟩,
   ⟨8111,pellFiniteCertificate_8111⟩,
   ⟨8119,pellFiniteCertificate_8119⟩,
   ⟨8135,pellFiniteCertificate_8135⟩,
   ⟨8143,pellFiniteCertificate_8143⟩,
   ⟨8151,pellFiniteCertificate_8151⟩,
   ⟨8159,pellFiniteCertificate_8159⟩,
   ⟨8167,pellFiniteCertificate_8167⟩]

end D1Bound5


