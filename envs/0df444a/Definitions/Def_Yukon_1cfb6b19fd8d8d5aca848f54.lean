-- Prove2me | Definitions.Def_Yukon_1cfb6b19fd8d8d5aca848f54
-- name    : Yukon_1cfb6b19fd8d8d5aca848f54
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T13:06:54.752454+00:00
-- url     : https://prove2.me/theorems/f09be650-632f-458f-9e5d-eeebdbe37991
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ReducedCommonLinear6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ReducedCommonLinear6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ReducedCommonLinear6807.lean
--
--   yukon-proof-operation:foundation-direct-c905a31aa172b2ddf5484837d8b7152becd258dc78677b15dde06819236691b0-parser-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjM3NmZiYzBkOWZmYWFiMWE5MGZhOGZjNDU1NTk3Zjg5YTU4MjZhMTY4OTlhYmYxOTNjYWVmMmYxMzQ4NzE0OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWM5MDVhMzFhYTE3MmIyZGRmNTQ4NDgzN2Q4YjcxNTJiZWNkMjU4ZGM3ODY3N2IxNWRkZTA2ODE5MjM2NjkxYjAtcGFyc2VyLXJldHJ5IiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fMWNmYjZiMTlmZDhkOGQ1YWNhODQ4ZjU0IiwidiI6Mn0]

import Definitions.Def_Yukon_760ec3cdedc56cac28a1993c

/-
UNCOMPILED. The shared linear values are constructed for the actual reduced
family and transported to the ORIGINAL first-tail components. No new budget
family is chosen and no first-cut cost bound is assumed.
-/


import Definitions.Def_Yukon_5c9a7a9d17b650621345d8aa














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ReducedCommonLinear6807
open scoped Classical BigOperators
open RCN159 RCN263 RCN086 RCN327
open RCN135 RCN136 RCN264 RCN243 RCN095 RCN237 RCN198 RCN275 RCN244
open RCN334 RCN332 RCN336 RCN338 RCN199 RCN207 RCN313 RCN341 RCN030
open LocatorHybridTransportC2 CommonLinearChannels6807 BoundaryTailReduced
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.ReducedCommonLinear6807.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.ReducedCommonLinear6807.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageErrorCap a b s : ℕ}

def reduced_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (reducedUnitFamily S hp hc hm) := by
  let A := reducedActiveGeometry S hp hc hm
  exact of_active_nested A.base A.hactive A.hZ
    (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
    S.irreducible_G (reducedFirstCut_proper S hp)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag (support a b s) (w+1))
      (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

def original_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)) :=
  of_congruent_cut (ordinary_sub_reducedFirstCut_dvd S)
    (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)
    (reduced_common S hp hc hm)

/-- The common flag coefficients lie in the image of `K[X]` (needed by the H-free bridge:
the derivation `d/dX` extends to them). -/
theorem original_common_lam_poly
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    (original_common S hp hc hm).lam ∈ Set.range (polynomialEmbedding K) :=
  (reducedActiveGeometry S hp hc hm).lam_poly

theorem original_common_mu_poly
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    (original_common S hp hc hm).mu ∈ Set.range (polynomialEmbedding K) :=
  (reducedActiveGeometry S hp hc hm).mu_poly

end
end ProximityPrize.SubmissionLower.ReducedCommonLinear6807


