-- Prove2me | Definitions.Def_Yukon_b6818e5220407b59d8d11637
-- name    : Yukon_b6818e5220407b59d8d11637
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T12:12:44.84002+00:00
-- url     : https://prove2.me/theorems/bf452810-9cf4-46e7-a577-cbfd15af91f2
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPairGeometry6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPairGeometry6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPairGeometry6814.lean
--
--   yukon-proof-operation:foundation-direct-94c13312fff0990084302b5a71cb5237f9d5401673cef0183ee08f6f204ca16e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOWY5NDY5MzUzOTE0M2UzMjkzMGU5NWVlOWUxNjlkZDY1OGFlZTFhY2Y0Y2M3YzJkZjkyMTg2NGUyMmY1ZmFjNiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTk0YzEzMzEyZmZmMDk5MDA4NDMwMmI1YTcxY2I1MjM3ZjlkNTQwMTY3M2NlZjAxODNlZTA4ZjZmMjA0Y2ExNmUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iNjgxOGU1MjIwNDA3YjU5ZDhkMTE2MzciLCJ2IjoyfQ]

import Definitions.Def_Yukon_5ead00dac98325c22e6d5e52

import Definitions.Def_Yukon_8aef1041375ab73b49f5291c


















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.Lower80889.Geometry
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain Counting BoundaryTailSharedDegreeBudget
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.Geometry.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.Geometry.instDecidableEqI : DecidableEq I := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.Geometry.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.Geometry.instStrongNormalizationMonoidP4 : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid




end
end ProximityPrize.SubmissionLower.Lower80889.Geometry

/-! The residual pair on the complement boxes of the universal flag. `Q = QB/H`
and `T = QA/H`, so every coordinate weight of `Q` and `T` is the product's weight
minus that of `H`, which is at least the universal flag `(r, y, t)`. The count
uses the carrier's left agreement caps only. -/
namespace ProximityPrize.SubmissionLower.Lower80889.PairCell
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN156 RCN167 RCN180 RCN234 RCN260 RCN294
open LocatorFactorAggregate LocatorBatchProductRoute LocatorBatchPhase6800
open Counting BoundaryTailSharedDegreeBudget BoundaryTailChainHelper AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PairCell.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PairCell.instDecidableEqI : DecidableEq I := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PairCell.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem degreeR_le (F : P4) : F.degreeOf 2 ≤ wt residualSWeights F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*0+d 2*1+d 3*0 ≤ wt residualSWeights F at h
  omega

theorem complement_weight (H G : P4) (hH : H ≠ 0) (hG : G ≠ 0)
    (U : Finset (RCN266.RegularIndex H)) (weights : Fin 4 → ℕ) :
    wt weights (regularProduct H U) + wt weights G ≤ wt weights (H*G) := by
  simp only [wt]
  rw [weightedTotalDegree_mul weights H G hH hG]
  exact Nat.add_le_add_right
    (weightedTotalDegree_le_of_dvd weights _ H (regularProduct_dvd_carrier H U) hH) _

/-- A cofactor of `H` in a flag box keeps only the complement of `H`'s universal flag. -/
theorem complement_degrees (H G : P4) (hH : H ≠ 0) (hG : G ≠ 0)
    (U : Finset (RCN266.RegularIndex H)) (D w L s : ℕ) (hD : 0 < D) (hw : 1 ≤ w)
    (hbox : H*G ∈ RCN100.globalCoefficientBox K D w L s) :
    G.degreeOf 1 ≤ (D-1+s)/w - middle (regularAggregateFlag H U) ∧
    G.degreeOf 2 ≤ s - (regularAggregateFlag H U).all ∧
    G.degreeOf 3 ≤ L - total (regularAggregateFlag H U) := by
  have hc := (mem_flagGlobalCoefficientBox_iff (H*G) D w L s hD).mp hbox
  have hyw := residualYS_mul_le_contact_add_slope (H*G) w hw
  have hy : wt residualYSWeights (H*G) ≤ (D-1+s)/w :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; omega)
  have e1 := complement_weight H G hH hG U residualYSWeights
  have e2 := complement_weight H G hH hG U residualSWeights
  have e3 := complement_weight H G hH hG U residualTotalWeights
  rw [← regularAggregateFlag_middle] at e1
  rw [← regularAggregateFlag_all] at e2
  rw [← regularAggregateFlag_total] at e3
  have d1 := Budgets.degreeY_le G
  have d2 := degreeR_le G
  have d3 := Budgets.degreeZ_le G
  omega

theorem pair_count_cell {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}
    (inp : Input u0 u1 selected Gamma) (H Q T : P4) (hH : H ≠ 0) (hQ : Q ≠ 0) (hT : T ≠ 0)
    (hrel : IsRelPrime Q T)
    (hQbox : H*Q ∈ RCN100.globalCoefficientBox K 24288170 131071 35527 40)
    (hTbox : H*T ∈ RCN100.globalCoefficientBox K 40963630 131071 10715 70)
    (U : Finset (RCN266.RegularIndex H)) (hr : (regularAggregateFlag H U).all < 40) :
    (∑ F : RCN052.RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) ≤
      PairCell6814.cap (regularAggregateFlag H U).all (middle (regularAggregateFlag H U))
        (total (regularAggregateFlag H U)) := by
  obtain ⟨qY, qR, qZ⟩ := complement_degrees H Q hH hQ U 24288170 131071 35527 40
    (by norm_num) (by norm_num) hQbox
  obtain ⟨tY, tR, tZ⟩ := complement_degrees H T hH hT U 40963630 131071 10715 70
    (by norm_num) (by norm_num) hTbox
  norm_num only at qY tY
  let P := PairCell6814.parameters (regularAggregateFlag H U).all
    (middle (regularAggregateFlag H U)) (total (regularAggregateFlag H U))
  have hly : 185 - middle (regularAggregateFlag H U) ≤ 185 := Nat.sub_le _ _
  have hlr : 40 - (regularAggregateFlag H U).all ≤ 40 := Nat.sub_le _ _
  have hlz : 35527 - total (regularAggregateFlag H U) ≤ 35527 := Nat.sub_le _ _
  have hry : 312 - middle (regularAggregateFlag H U) ≤ 312 := Nat.sub_le _ _
  have hrr : 70 - (regularAggregateFlag H U).all ≤ 70 := Nat.sub_le _ _
  have hrz : 10715 - total (regularAggregateFlag H U) ≤ 10715 := Nat.sub_le _ _
  have hcount (F : RCN052.RegularIndex Q) := regularPairSeeds_bound_left P Q T hrel F 2130706433
    ((degreeOf_le_of_dvd 1 F.1 Q (positiveRFactors_spec _ _ F.2).2.1 hQ).trans qY)
    ((degreeOf_le_of_dvd 2 F.1 Q (positiveRFactors_spec _ _ F.2).2.1 hQ).trans qR)
    ((degreeOf_le_of_dvd 3 F.1 Q (positiveRFactors_spec _ _ F.2).2.1 hQ).trans qZ)
    tY tR tZ (by dsimp only [P, PairCell6814.parameters]; omega)
    (by dsimp only [P, PairCell6814.parameters]; omega)
    (by dsimp only [P, PairCell6814.parameters]; omega)
    (by dsimp only [P, PairCell6814.parameters]; omega)
    (by
      dsimp only [P, PairCell6814.parameters, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hlr hrz) (Nat.mul_le_mul hlz hrr)).trans_lt
        (by norm_num))
    (by
      dsimp only [P, PairCell6814.parameters, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hly hrz) (Nat.mul_le_mul hlz hry)).trans_lt
        (by norm_num))
    (by
      dsimp only [P, PairCell6814.parameters, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hly hrr) (Nat.mul_le_mul hlr hry)).trans_lt
        (by norm_num))
    selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by rw [Finset.card_univ]; exact Fintype.card_fin _)
    (by norm_num [P, PairCell6814.parameters]) (by norm_num [P, PairCell6814.parameters])
    (by norm_num [P, PairCell6814.parameters]) (by norm_num [P, PairCell6814.parameters])
    inp.degree inp.agreement
    (by simpa only [P, PairCell6814.parameters, UnequalParameters.errors,
      (show (262144 - 181255 : ℕ) = 80889 by decide +kernel)] using inp.noPencil)
  have hsum := sum_regular_counts_bound_left P Q T selected Gamma
    (regularVector_budgets_actual P Q hQ qY qR qZ) hcount
  exact (Nat.le_div_iff_mul_le (by norm_num [P, PairCell6814.parameters, UnequalParameters.gap])).mpr hsum

end
end ProximityPrize.SubmissionLower.Lower80889.PairCell


