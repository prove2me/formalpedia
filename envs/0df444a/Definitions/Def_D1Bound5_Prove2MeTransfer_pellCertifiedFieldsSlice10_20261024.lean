-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice10_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice10_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:16:50.66401+00:00
-- url     : https://prove2.me/theorems/3d32b882-d99b-4340-a873-c1c51fa50f0a
-- title:
--   Exact Pell certificate records 641–704
-- statement:
--   The exact consecutive certificate records 641 through 704 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_011

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice10_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨6295,pellFiniteCertificate_6295⟩,
   ⟨6303,pellFiniteCertificate_6303⟩,
   ⟨6311,pellFiniteCertificate_6311⟩,
   ⟨6319,pellFiniteCertificate_6319⟩,
   ⟨6335,pellFiniteCertificate_6335⟩,
   ⟨6343,pellFiniteCertificate_6343⟩,
   ⟨6351,pellFiniteCertificate_6351⟩,
   ⟨6359,pellFiniteCertificate_6359⟩,
   ⟨6367,pellFiniteCertificate_6367⟩,
   ⟨6383,pellFiniteCertificate_6383⟩,
   ⟨6391,pellFiniteCertificate_6391⟩,
   ⟨6407,pellFiniteCertificate_6407⟩,
   ⟨6415,pellFiniteCertificate_6415⟩,
   ⟨6423,pellFiniteCertificate_6423⟩,
   ⟨6431,pellFiniteCertificate_6431⟩,
   ⟨6439,pellFiniteCertificate_6439⟩,
   ⟨6447,pellFiniteCertificate_6447⟩,
   ⟨6455,pellFiniteCertificate_6455⟩,
   ⟨6463,pellFiniteCertificate_6463⟩,
   ⟨6479,pellFiniteCertificate_6479⟩,
   ⟨6487,pellFiniteCertificate_6487⟩,
   ⟨6495,pellFiniteCertificate_6495⟩,
   ⟨6503,pellFiniteCertificate_6503⟩,
   ⟨6511,pellFiniteCertificate_6511⟩,
   ⟨6519,pellFiniteCertificate_6519⟩,
   ⟨6527,pellFiniteCertificate_6527⟩,
   ⟨6535,pellFiniteCertificate_6535⟩,
   ⟨6551,pellFiniteCertificate_6551⟩,
   ⟨6559,pellFiniteCertificate_6559⟩,
   ⟨6567,pellFiniteCertificate_6567⟩,
   ⟨6583,pellFiniteCertificate_6583⟩,
   ⟨6599,pellFiniteCertificate_6599⟩,
   ⟨6607,pellFiniteCertificate_6607⟩,
   ⟨6623,pellFiniteCertificate_6623⟩,
   ⟨6631,pellFiniteCertificate_6631⟩,
   ⟨6639,pellFiniteCertificate_6639⟩,
   ⟨6663,pellFiniteCertificate_6663⟩,
   ⟨6671,pellFiniteCertificate_6671⟩,
   ⟨6679,pellFiniteCertificate_6679⟩,
   ⟨6695,pellFiniteCertificate_6695⟩,
   ⟨6703,pellFiniteCertificate_6703⟩,
   ⟨6711,pellFiniteCertificate_6711⟩,
   ⟨6719,pellFiniteCertificate_6719⟩,
   ⟨6735,pellFiniteCertificate_6735⟩,
   ⟨6743,pellFiniteCertificate_6743⟩,
   ⟨6751,pellFiniteCertificate_6751⟩,
   ⟨6767,pellFiniteCertificate_6767⟩,
   ⟨6783,pellFiniteCertificate_6783⟩,
   ⟨6791,pellFiniteCertificate_6791⟩,
   ⟨6799,pellFiniteCertificate_6799⟩,
   ⟨6807,pellFiniteCertificate_6807⟩,
   ⟨6815,pellFiniteCertificate_6815⟩,
   ⟨6823,pellFiniteCertificate_6823⟩,
   ⟨6839,pellFiniteCertificate_6839⟩,
   ⟨6847,pellFiniteCertificate_6847⟩,
   ⟨6855,pellFiniteCertificate_6855⟩,
   ⟨6863,pellFiniteCertificate_6863⟩,
   ⟨6871,pellFiniteCertificate_6871⟩,
   ⟨6879,pellFiniteCertificate_6879⟩,
   ⟨6887,pellFiniteCertificate_6887⟩,
   ⟨6895,pellFiniteCertificate_6895⟩,
   ⟨6911,pellFiniteCertificate_6911⟩,
   ⟨6919,pellFiniteCertificate_6919⟩,
   ⟨6927,pellFiniteCertificate_6927⟩]

end D1Bound5


