-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice05_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice05_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:41.720529+00:00
-- url     : https://prove2.me/theorems/fa4d92d1-3da6-4dc3-88b4-bf807601cbbd
-- title:
--   Exact Pell certificate records 321–384
-- statement:
--   The exact consecutive certificate records 321 through 384 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_006
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_007

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice05_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨3135,pellFiniteCertificate_3135⟩,
   ⟨3143,pellFiniteCertificate_3143⟩,
   ⟨3151,pellFiniteCertificate_3151⟩,
   ⟨3167,pellFiniteCertificate_3167⟩,
   ⟨3183,pellFiniteCertificate_3183⟩,
   ⟨3191,pellFiniteCertificate_3191⟩,
   ⟨3199,pellFiniteCertificate_3199⟩,
   ⟨3207,pellFiniteCertificate_3207⟩,
   ⟨3215,pellFiniteCertificate_3215⟩,
   ⟨3223,pellFiniteCertificate_3223⟩,
   ⟨3239,pellFiniteCertificate_3239⟩,
   ⟨3247,pellFiniteCertificate_3247⟩,
   ⟨3255,pellFiniteCertificate_3255⟩,
   ⟨3263,pellFiniteCertificate_3263⟩,
   ⟨3271,pellFiniteCertificate_3271⟩,
   ⟨3279,pellFiniteCertificate_3279⟩,
   ⟨3287,pellFiniteCertificate_3287⟩,
   ⟨3295,pellFiniteCertificate_3295⟩,
   ⟨3311,pellFiniteCertificate_3311⟩,
   ⟨3319,pellFiniteCertificate_3319⟩,
   ⟨3327,pellFiniteCertificate_3327⟩,
   ⟨3335,pellFiniteCertificate_3335⟩,
   ⟨3343,pellFiniteCertificate_3343⟩,
   ⟨3351,pellFiniteCertificate_3351⟩,
   ⟨3359,pellFiniteCertificate_3359⟩,
   ⟨3367,pellFiniteCertificate_3367⟩,
   ⟨3383,pellFiniteCertificate_3383⟩,
   ⟨3391,pellFiniteCertificate_3391⟩,
   ⟨3399,pellFiniteCertificate_3399⟩,
   ⟨3407,pellFiniteCertificate_3407⟩,
   ⟨3415,pellFiniteCertificate_3415⟩,
   ⟨3423,pellFiniteCertificate_3423⟩,
   ⟨3431,pellFiniteCertificate_3431⟩,
   ⟨3439,pellFiniteCertificate_3439⟩,
   ⟨3455,pellFiniteCertificate_3455⟩,
   ⟨3463,pellFiniteCertificate_3463⟩,
   ⟨3471,pellFiniteCertificate_3471⟩,
   ⟨3487,pellFiniteCertificate_3487⟩,
   ⟨3495,pellFiniteCertificate_3495⟩,
   ⟨3503,pellFiniteCertificate_3503⟩,
   ⟨3511,pellFiniteCertificate_3511⟩,
   ⟨3527,pellFiniteCertificate_3527⟩,
   ⟨3535,pellFiniteCertificate_3535⟩,
   ⟨3543,pellFiniteCertificate_3543⟩,
   ⟨3551,pellFiniteCertificate_3551⟩,
   ⟨3559,pellFiniteCertificate_3559⟩,
   ⟨3567,pellFiniteCertificate_3567⟩,
   ⟨3583,pellFiniteCertificate_3583⟩,
   ⟨3599,pellFiniteCertificate_3599⟩,
   ⟨3607,pellFiniteCertificate_3607⟩,
   ⟨3615,pellFiniteCertificate_3615⟩,
   ⟨3623,pellFiniteCertificate_3623⟩,
   ⟨3631,pellFiniteCertificate_3631⟩,
   ⟨3639,pellFiniteCertificate_3639⟩,
   ⟨3647,pellFiniteCertificate_3647⟩,
   ⟨3655,pellFiniteCertificate_3655⟩,
   ⟨3671,pellFiniteCertificate_3671⟩,
   ⟨3679,pellFiniteCertificate_3679⟩,
   ⟨3687,pellFiniteCertificate_3687⟩,
   ⟨3695,pellFiniteCertificate_3695⟩,
   ⟨3711,pellFiniteCertificate_3711⟩,
   ⟨3719,pellFiniteCertificate_3719⟩,
   ⟨3727,pellFiniteCertificate_3727⟩,
   ⟨3743,pellFiniteCertificate_3743⟩]

end D1Bound5


