-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice07_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice07_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:49.43279+00:00
-- url     : https://prove2.me/theorems/80451033-3fb3-4156-aebd-7f488273fb77
-- title:
--   Exact Pell certificate records 449–512
-- statement:
--   The exact consecutive certificate records 449 through 512 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_001
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_008

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice07_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨4407,pellFiniteCertificate_4407⟩,
   ⟨4415,pellFiniteCertificate_4415⟩,
   ⟨4423,pellFiniteCertificate_4423⟩,
   ⟨4431,pellFiniteCertificate_4431⟩,
   ⟨4439,pellFiniteCertificate_4439⟩,
   ⟨4447,pellFiniteCertificate_4447⟩,
   ⟨4463,pellFiniteCertificate_4463⟩,
   ⟨4471,pellFiniteCertificate_4471⟩,
   ⟨4479,pellFiniteCertificate_4479⟩,
   ⟨4487,pellFiniteCertificate_4487⟩,
   ⟨4495,pellFiniteCertificate_4495⟩,
   ⟨4503,pellFiniteCertificate_4503⟩,
   ⟨4511,pellFiniteCertificate_4511⟩,
   ⟨4519,pellFiniteCertificate_4519⟩,
   ⟨4535,pellFiniteCertificate_4535⟩,
   ⟨4543,pellFiniteCertificate_4543⟩,
   ⟨4551,pellFiniteCertificate_4551⟩,
   ⟨4559,pellFiniteCertificate_4559⟩,
   ⟨4567,pellFiniteCertificate_4567⟩,
   ⟨4583,pellFiniteCertificate_4583⟩,
   ⟨4591,pellFiniteCertificate_4591⟩,
   ⟨4607,pellFiniteCertificate_4607⟩,
   ⟨4615,pellFiniteCertificate_4615⟩,
   ⟨4623,pellFiniteCertificate_4623⟩,
   ⟨4631,pellFiniteCertificate_4631⟩,
   ⟨4639,pellFiniteCertificate_4639⟩,
   ⟨4647,pellFiniteCertificate_4647⟩,
   ⟨4663,pellFiniteCertificate_4663⟩,
   ⟨4679,pellFiniteCertificate_4679⟩,
   ⟨4687,pellFiniteCertificate_4687⟩,
   ⟨4695,pellFiniteCertificate_4695⟩,
   ⟨4703,pellFiniteCertificate_4703⟩,
   ⟨4711,pellFiniteCertificate_4711⟩,
   ⟨4727,pellFiniteCertificate_4727⟩,
   ⟨4735,pellFiniteCertificate_4735⟩,
   ⟨4751,pellFiniteCertificate_4751⟩,
   ⟨4759,pellFiniteCertificate_4759⟩,
   ⟨4767,pellFiniteCertificate_4767⟩,
   ⟨4783,pellFiniteCertificate_4783⟩,
   ⟨4791,pellFiniteCertificate_4791⟩,
   ⟨4799,pellFiniteCertificate_4799⟩,
   ⟨4807,pellFiniteCertificate_4807⟩,
   ⟨4823,pellFiniteCertificate_4823⟩,
   ⟨4831,pellFiniteCertificate_4831⟩,
   ⟨4839,pellFiniteCertificate_4839⟩,
   ⟨4847,pellFiniteCertificate_4847⟩,
   ⟨4855,pellFiniteCertificate_4855⟩,
   ⟨4863,pellFiniteCertificate_4863⟩,
   ⟨4871,pellFiniteCertificate_4871⟩,
   ⟨4879,pellFiniteCertificate_4879⟩,
   ⟨4895,pellFiniteCertificate_4895⟩,
   ⟨4903,pellFiniteCertificate_4903⟩,
   ⟨4911,pellFiniteCertificate_4911⟩,
   ⟨4919,pellFiniteCertificate_4919⟩,
   ⟨4927,pellFiniteCertificate_4927⟩,
   ⟨4935,pellFiniteCertificate_4935⟩,
   ⟨4943,pellFiniteCertificate_4943⟩,
   ⟨4951,pellFiniteCertificate_4951⟩,
   ⟨4967,pellFiniteCertificate_4967⟩,
   ⟨4983,pellFiniteCertificate_4983⟩,
   ⟨4991,pellFiniteCertificate_4991⟩,
   ⟨4999,pellFiniteCertificate_4999⟩,
   ⟨5007,pellFiniteCertificate_5007⟩,
   ⟨5015,pellFiniteCertificate_5015⟩]

end D1Bound5


