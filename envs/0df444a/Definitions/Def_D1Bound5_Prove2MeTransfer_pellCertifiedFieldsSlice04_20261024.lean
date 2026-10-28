-- Prove2me | Definitions.Def_D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice04_20261024
-- name    : D1Bound5_Prove2MeTransfer_pellCertifiedFieldsSlice04_20261024
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T07:17:34.435431+00:00
-- url     : https://prove2.me/theorems/116c2c12-fe97-4323-8c05-33aa1630980a
-- title:
--   Exact Pell certificate records 257–320
-- statement:
--   The exact consecutive certificate records 257 through 320 of pellCertifiedFields. Their ordered concatenation preserves the original dependent pairs and certificates.
-- source:
--   D1Bound5/PellFiniteFieldCoverageData.lean, lines 8-1024, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1026-1027, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1029-1033, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91; D1Bound5/PellFiniteFieldCoverageData.lean, lines 1035-1037, SHA-256 b122fbf2e6836b571802585cfe63285a119fb29e8151c681d18d1e0e2049bd91. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_005
import Definitions.Def_D1Bound5_PellLightAllFiniteCertificates_Definitions_006

namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def Prove2MeTransfer.pellCertifiedFieldsSlice04_20261024 : List (Σ d : ℤ, PellFiniteCertificate d (10^275)) :=
  [⟨2495,pellFiniteCertificate_2495⟩,
   ⟨2503,pellFiniteCertificate_2503⟩,
   ⟨2519,pellFiniteCertificate_2519⟩,
   ⟨2543,pellFiniteCertificate_2543⟩,
   ⟨2551,pellFiniteCertificate_2551⟩,
   ⟨2559,pellFiniteCertificate_2559⟩,
   ⟨2567,pellFiniteCertificate_2567⟩,
   ⟨2591,pellFiniteCertificate_2591⟩,
   ⟨2599,pellFiniteCertificate_2599⟩,
   ⟨2607,pellFiniteCertificate_2607⟩,
   ⟨2615,pellFiniteCertificate_2615⟩,
   ⟨2623,pellFiniteCertificate_2623⟩,
   ⟨2631,pellFiniteCertificate_2631⟩,
   ⟨2639,pellFiniteCertificate_2639⟩,
   ⟨2647,pellFiniteCertificate_2647⟩,
   ⟨2663,pellFiniteCertificate_2663⟩,
   ⟨2671,pellFiniteCertificate_2671⟩,
   ⟨2679,pellFiniteCertificate_2679⟩,
   ⟨2687,pellFiniteCertificate_2687⟩,
   ⟨2703,pellFiniteCertificate_2703⟩,
   ⟨2711,pellFiniteCertificate_2711⟩,
   ⟨2719,pellFiniteCertificate_2719⟩,
   ⟨2735,pellFiniteCertificate_2735⟩,
   ⟨2743,pellFiniteCertificate_2743⟩,
   ⟨2751,pellFiniteCertificate_2751⟩,
   ⟨2759,pellFiniteCertificate_2759⟩,
   ⟨2767,pellFiniteCertificate_2767⟩,
   ⟨2791,pellFiniteCertificate_2791⟩,
   ⟨2807,pellFiniteCertificate_2807⟩,
   ⟨2815,pellFiniteCertificate_2815⟩,
   ⟨2823,pellFiniteCertificate_2823⟩,
   ⟨2831,pellFiniteCertificate_2831⟩,
   ⟨2839,pellFiniteCertificate_2839⟩,
   ⟨2847,pellFiniteCertificate_2847⟩,
   ⟨2855,pellFiniteCertificate_2855⟩,
   ⟨2863,pellFiniteCertificate_2863⟩,
   ⟨2879,pellFiniteCertificate_2879⟩,
   ⟨2887,pellFiniteCertificate_2887⟩,
   ⟨2895,pellFiniteCertificate_2895⟩,
   ⟨2903,pellFiniteCertificate_2903⟩,
   ⟨2911,pellFiniteCertificate_2911⟩,
   ⟨2919,pellFiniteCertificate_2919⟩,
   ⟨2927,pellFiniteCertificate_2927⟩,
   ⟨2935,pellFiniteCertificate_2935⟩,
   ⟨2951,pellFiniteCertificate_2951⟩,
   ⟨2959,pellFiniteCertificate_2959⟩,
   ⟨2967,pellFiniteCertificate_2967⟩,
   ⟨2983,pellFiniteCertificate_2983⟩,
   ⟨2991,pellFiniteCertificate_2991⟩,
   ⟨2999,pellFiniteCertificate_2999⟩,
   ⟨3007,pellFiniteCertificate_3007⟩,
   ⟨3023,pellFiniteCertificate_3023⟩,
   ⟨3031,pellFiniteCertificate_3031⟩,
   ⟨3039,pellFiniteCertificate_3039⟩,
   ⟨3047,pellFiniteCertificate_3047⟩,
   ⟨3055,pellFiniteCertificate_3055⟩,
   ⟨3063,pellFiniteCertificate_3063⟩,
   ⟨3071,pellFiniteCertificate_3071⟩,
   ⟨3079,pellFiniteCertificate_3079⟩,
   ⟨3095,pellFiniteCertificate_3095⟩,
   ⟨3103,pellFiniteCertificate_3103⟩,
   ⟨3111,pellFiniteCertificate_3111⟩,
   ⟨3119,pellFiniteCertificate_3119⟩,
   ⟨3127,pellFiniteCertificate_3127⟩]

end D1Bound5


