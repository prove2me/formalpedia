-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice06_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice06_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:19:25.005803+00:00
-- url     : https://prove2.me/theorems/8e9a5638-a5c5-42ad-878e-a36d79723259
-- title:
--   Exact Pell certificate records 385–448
-- statement:
--   The exact consecutive certificate records 385 through 448 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_007
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_008

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice06_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨3759,pellFiniteCertificate_3759⟩,
   ⟨3767,pellFiniteCertificate_3767⟩,
   ⟨3783,pellFiniteCertificate_3783⟩,
   ⟨3791,pellFiniteCertificate_3791⟩,
   ⟨3799,pellFiniteCertificate_3799⟩,
   ⟨3815,pellFiniteCertificate_3815⟩,
   ⟨3823,pellFiniteCertificate_3823⟩,
   ⟨3831,pellFiniteCertificate_3831⟩,
   ⟨3839,pellFiniteCertificate_3839⟩,
   ⟨3847,pellFiniteCertificate_3847⟩,
   ⟨3855,pellFiniteCertificate_3855⟩,
   ⟨3863,pellFiniteCertificate_3863⟩,
   ⟨3895,pellFiniteCertificate_3895⟩,
   ⟨3903,pellFiniteCertificate_3903⟩,
   ⟨3911,pellFiniteCertificate_3911⟩,
   ⟨3919,pellFiniteCertificate_3919⟩,
   ⟨3927,pellFiniteCertificate_3927⟩,
   ⟨3935,pellFiniteCertificate_3935⟩,
   ⟨3943,pellFiniteCertificate_3943⟩,
   ⟨3959,pellFiniteCertificate_3959⟩,
   ⟨3967,pellFiniteCertificate_3967⟩,
   ⟨3983,pellFiniteCertificate_3983⟩,
   ⟨3991,pellFiniteCertificate_3991⟩,
   ⟨3999,pellFiniteCertificate_3999⟩,
   ⟨4007,pellFiniteCertificate_4007⟩,
   ⟨4015,pellFiniteCertificate_4015⟩,
   ⟨4031,pellFiniteCertificate_4031⟩,
   ⟨4039,pellFiniteCertificate_4039⟩,
   ⟨4047,pellFiniteCertificate_4047⟩,
   ⟨4055,pellFiniteCertificate_4055⟩,
   ⟨4063,pellFiniteCertificate_4063⟩,
   ⟨4071,pellFiniteCertificate_4071⟩,
   ⟨4079,pellFiniteCertificate_4079⟩,
   ⟨4087,pellFiniteCertificate_4087⟩,
   ⟨4103,pellFiniteCertificate_4103⟩,
   ⟨4111,pellFiniteCertificate_4111⟩,
   ⟨4119,pellFiniteCertificate_4119⟩,
   ⟨4127,pellFiniteCertificate_4127⟩,
   ⟨4135,pellFiniteCertificate_4135⟩,
   ⟨4143,pellFiniteCertificate_4143⟩,
   ⟨4151,pellFiniteCertificate_4151⟩,
   ⟨4159,pellFiniteCertificate_4159⟩,
   ⟨4183,pellFiniteCertificate_4183⟩,
   ⟨4191,pellFiniteCertificate_4191⟩,
   ⟨4199,pellFiniteCertificate_4199⟩,
   ⟨4207,pellFiniteCertificate_4207⟩,
   ⟨4215,pellFiniteCertificate_4215⟩,
   ⟨4223,pellFiniteCertificate_4223⟩,
   ⟨4231,pellFiniteCertificate_4231⟩,
   ⟨4247,pellFiniteCertificate_4247⟩,
   ⟨4255,pellFiniteCertificate_4255⟩,
   ⟨4271,pellFiniteCertificate_4271⟩,
   ⟨4279,pellFiniteCertificate_4279⟩,
   ⟨4287,pellFiniteCertificate_4287⟩,
   ⟨4295,pellFiniteCertificate_4295⟩,
   ⟨4303,pellFiniteCertificate_4303⟩,
   ⟨4319,pellFiniteCertificate_4319⟩,
   ⟨4327,pellFiniteCertificate_4327⟩,
   ⟨4343,pellFiniteCertificate_4343⟩,
   ⟨4351,pellFiniteCertificate_4351⟩,
   ⟨4359,pellFiniteCertificate_4359⟩,
   ⟨4367,pellFiniteCertificate_4367⟩,
   ⟨4391,pellFiniteCertificate_4391⟩,
   ⟨4399,pellFiniteCertificate_4399⟩]

end D1Bound5


