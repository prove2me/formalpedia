-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice01_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice01_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:57.586667+00:00
-- url     : https://prove2.me/theorems/7701bdd8-354c-4d80-84d5-5b602d0ff787
-- title:
--   Exact Pell certificate records 65–128
-- statement:
--   The exact consecutive certificate records 65 through 128 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_002
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_003

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice01_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨615,pellFiniteCertificate_615⟩,
   ⟨623,pellFiniteCertificate_623⟩,
   ⟨631,pellFiniteCertificate_631⟩,
   ⟨647,pellFiniteCertificate_647⟩,
   ⟨655,pellFiniteCertificate_655⟩,
   ⟨663,pellFiniteCertificate_663⟩,
   ⟨671,pellFiniteCertificate_671⟩,
   ⟨679,pellFiniteCertificate_679⟩,
   ⟨687,pellFiniteCertificate_687⟩,
   ⟨695,pellFiniteCertificate_695⟩,
   ⟨703,pellFiniteCertificate_703⟩,
   ⟨719,pellFiniteCertificate_719⟩,
   ⟨727,pellFiniteCertificate_727⟩,
   ⟨743,pellFiniteCertificate_743⟩,
   ⟨751,pellFiniteCertificate_751⟩,
   ⟨759,pellFiniteCertificate_759⟩,
   ⟨767,pellFiniteCertificate_767⟩,
   ⟨791,pellFiniteCertificate_791⟩,
   ⟨799,pellFiniteCertificate_799⟩,
   ⟨807,pellFiniteCertificate_807⟩,
   ⟨815,pellFiniteCertificate_815⟩,
   ⟨823,pellFiniteCertificate_823⟩,
   ⟨831,pellFiniteCertificate_831⟩,
   ⟨839,pellFiniteCertificate_839⟩,
   ⟨863,pellFiniteCertificate_863⟩,
   ⟨871,pellFiniteCertificate_871⟩,
   ⟨879,pellFiniteCertificate_879⟩,
   ⟨887,pellFiniteCertificate_887⟩,
   ⟨895,pellFiniteCertificate_895⟩,
   ⟨903,pellFiniteCertificate_903⟩,
   ⟨911,pellFiniteCertificate_911⟩,
   ⟨919,pellFiniteCertificate_919⟩,
   ⟨935,pellFiniteCertificate_935⟩,
   ⟨943,pellFiniteCertificate_943⟩,
   ⟨951,pellFiniteCertificate_951⟩,
   ⟨959,pellFiniteCertificate_959⟩,
   ⟨967,pellFiniteCertificate_967⟩,
   ⟨983,pellFiniteCertificate_983⟩,
   ⟨991,pellFiniteCertificate_991⟩,
   ⟨1007,pellFiniteCertificate_1007⟩,
   ⟨1015,pellFiniteCertificate_1015⟩,
   ⟨1023,pellFiniteCertificate_1023⟩,
   ⟨1031,pellFiniteCertificate_1031⟩,
   ⟨1039,pellFiniteCertificate_1039⟩,
   ⟨1047,pellFiniteCertificate_1047⟩,
   ⟨1055,pellFiniteCertificate_1055⟩,
   ⟨1063,pellFiniteCertificate_1063⟩,
   ⟨1079,pellFiniteCertificate_1079⟩,
   ⟨1087,pellFiniteCertificate_1087⟩,
   ⟨1095,pellFiniteCertificate_1095⟩,
   ⟨1103,pellFiniteCertificate_1103⟩,
   ⟨1111,pellFiniteCertificate_1111⟩,
   ⟨1119,pellFiniteCertificate_1119⟩,
   ⟨1135,pellFiniteCertificate_1135⟩,
   ⟨1151,pellFiniteCertificate_1151⟩,
   ⟨1159,pellFiniteCertificate_1159⟩,
   ⟨1167,pellFiniteCertificate_1167⟩,
   ⟨1191,pellFiniteCertificate_1191⟩,
   ⟨1199,pellFiniteCertificate_1199⟩,
   ⟨1207,pellFiniteCertificate_1207⟩,
   ⟨1223,pellFiniteCertificate_1223⟩,
   ⟨1231,pellFiniteCertificate_1231⟩,
   ⟨1239,pellFiniteCertificate_1239⟩,
   ⟨1247,pellFiniteCertificate_1247⟩]

end D1Bound5


