-- Prove2me | Definitions.Def_Yukon_a1c6df01b9cf85d860560491
-- name    : Yukon_a1c6df01b9cf85d860560491
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:56:50.946226+00:00
-- url     : https://prove2.me/theorems/3246468c-067d-44f9-8f50-d04df9e08f09
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.FoldChainCounting6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.FoldChainCounting6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/FoldChainCounting6814.lean
--
--   yukon-proof-operation:foundation-direct-3cc374c82493f948efcefbf37a2cd190170e0574c8ff3e9ab111f6a0429eee11
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzEyYWEwMzRlYWM3ZWRiOTQwZDA5NmQxMzU5NTM5ZDY1Y2JiODBmZjQ4MjAzM2FlZmE3NzZiZTZjZGI1ZDcyYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTNjYzM3NGM4MjQ5M2Y5NDhlZmNlZmJmMzdhMmNkMTkwMTcwZTA1NzRjOGZmM2U5YWIxMTFmNmEwNDI5ZWVlMTEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hMWM2ZGYwMWI5Y2Y4NWQ4NjA1NjA0OTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_5ead00dac98325c22e6d5e52

import Definitions.Def_Yukon_d60e90233ae74257508ecaaf

import Definitions.Def_Yukon_7911c456bc993ce0ea552cc2



















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Factor charges with the fold-chain bound. The derivative stages of a
factor are replaced by its fold seeds, counted once on the fold curve, so the
charge `|foldSeeds| + |tailSeeds|` is affine in the `R`-degree and
`FoldChainPolynomial6814.foldUnit` bounds it per unit of `R`-degree. -/

namespace ProximityPrize.SubmissionLower.Lower80889.FoldCounting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238
  RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80889
  BoundaryTailChainHelper AsymmetricHelper FoldChain6813 FoldChainPolynomial6814 Counting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldCounting.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldCounting.instDecidableEqI : DecidableEq I := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldCounting.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldCounting.instStrongNormalizationMonoidP4 : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

def factorCharge' (F : P4) (selected : K → Polynomial K) (Gamma : Finset K) : ℕ :=
  (foldSeeds F selected Gamma).card + (tailSeeds F selected Gamma).card

theorem factorCharge'_le_unit' (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : Irreducible F) (hpos : 0 < F.degreeOf 2)
    (hbox : F ∈ RCN174.globalCoefficientBox K 24288170 131071 35527 40)
    (y z r : ℕ) (hy : y ≤ 185) (hz : z ≤ 35527) (hr : r ≤ 40)
    (hFY : F.degreeOf 1 ≤ y) (hFZ : F.degreeOf 3 ≤ z) (hFR : F.degreeOf 2 ≤ r) :
    factorCharge' F selected Gamma ≤ F.degreeOf 2 * (foldUnit y z r + 4502611644209) := by
  have htail := factor_tail_count inp F hF.ne_zero hbox
  have hT := tail_le_foldUnit y z r
  by_cases h1 : F.degreeOf 2 = 1
  · rw [factorCharge', foldSeeds_eq_empty_of_degree_one F h1, Finset.card_empty, h1]
    omega
  have hd : 2 ≤ F.degreeOf 2 := by omega
  have hd40 : F.degreeOf 2 ≤ 40 := hFR.trans hr
  have hleft : F.degreeOf 2 - 1 ≤ 40 := by omega
  have hfold := foldSeeds_card_le_left (stage y z (F.degreeOf 2) 1) F hF 2130706433
    hpos (hd40.trans_lt (by decide +kernel))
    hFY (by dsimp [stage]; omega) hFZ hFY (by dsimp [stage]; omega) hFZ
    (by dsimp [stage]; omega)
    ((hy.trans_lt (by decide +kernel) : y < 2130706433))
    ((hd40.trans_lt (by decide +kernel) : F.degreeOf 2 < 2130706433))
    ((hz.trans_lt (by decide +kernel) : z < 2130706433))
    (by
      dsimp [stage, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hleft hz) (Nat.mul_le_mul hz hd40)).trans_lt
        (by decide +kernel))
    (by
      dsimp [stage, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hy hz) (Nat.mul_le_mul hz hy)).trans_lt
        (by decide +kernel))
    (by
      dsimp [stage, UnequalParameters.mixedCost]
      exact (Nat.add_le_add (Nat.mul_le_mul hy hd40) (Nat.mul_le_mul hleft hy)).trans_lt
        (by decide +kernel))
    selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
    (by rw [Finset.card_univ]; exact Fintype.card_fin _)
    (by norm_num [stage]) (by norm_num [stage]) (by norm_num [stage]) (by norm_num [stage])
    inp.degree inp.agreement
    (by simpa only [stage, UnequalParameters.errors,
      (show (262144 - 181255 : ℕ) = 80889 by decide +kernel)] using inp.noPencil)
  have hgap : (stage y z (F.degreeOf 2) 1).gap = 50184 := by
    simp [stage, UnequalParameters.gap]
  have hdot : dot ⟨(stage y z (F.degreeOf 2) 1).leftY, (stage y z (F.degreeOf 2) 1).leftR,
      (stage y z (F.degreeOf 2) 1).leftZ⟩ (stage y z (F.degreeOf 2) 1).mixedCost =
        y*z*(6*F.degreeOf 2-4) := stageDot y z (F.degreeOf 2) (by omega)
  rw [hgap, hdot] at hfold
  have hnum := foldNumerator_le_unit y z (F.degreeOf 2) r hd hFR
  unfold foldNumerator at hnum
  have hs : 4502611644209 ≤ F.degreeOf 2 * 4502611644209 :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmul : factorCharge' F selected Gamma * 50184 ≤
      F.degreeOf 2 * (foldUnit y z r + 4502611644209) * 50184 := by
    unfold factorCharge'
    nlinarith
  exact Nat.le_of_mul_le_mul_right hmul (by decide)

end
end ProximityPrize.SubmissionLower.Lower80889.FoldCounting

namespace ProximityPrize.SubmissionLower.Lower80889.FoldBudgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting Budgets
  BoundaryTailSharedDegreeBudget FoldChainPolynomial6814 FoldCounting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldBudgets.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldBudgets.instDecidableEqI : DecidableEq I := Classical.decEq _

theorem joint_charge' (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 24288170 131071 35527 40)
    (hHbox : H ∈ RCN174.globalCoefficientBox K 24288170 131071 35527 40)
    (hQbox : Q ∈ RCN174.globalCoefficientBox K 24288170 131071 35527 40)
    (U : Finset (RegularIndex H)) (u0 u1 : I → K) (selected : K → Polynomial K)
    (Gamma Delta : Finset K) (inpH : Input u0 u1 selected Gamma) (inpQ : Input u0 u1 selected Delta)
    (hr : (regularAggregateFlag H U).all ≤ 37)
    (hy : middle (regularAggregateFlag H U) ≤ 175)
    (ht : total (regularAggregateFlag H U) ≤ 10714) :
    let p := regularAggregateFlag H U
    (∑ F : RegularIndex H, factorCharge' F.1 selected Gamma) +
      (∑ F : RegularIndex Q, factorCharge' F.1 selected Delta) ≤
      p.all*foldUnit (middle p) (total p) p.all +
      (40-p.all)*foldUnit (185-middle p) (35527-total p) (40-p.all) + 40*4502611644209 := by
  let p := regularAggregateFlag H U
  let N := (Finset.univ : Finset (RegularIndex H)) \ U
  have hb := aggregate_pair_caps H Q hH hQ hbox
  have hs := split_aggregate H U
  have hnR : (regularAggregateFlag H N).all ≤ 40-p.all := by dsimp only [p,N]; omega
  have hnY : middle (regularAggregateFlag H N) ≤ 185-middle p := by dsimp only [p,N]; omega
  have hnT : total (regularAggregateFlag H N) ≤ 35527-total p := by dsimp only [p,N]; omega
  have hqR : (regularAggregateFlag Q Finset.univ).all ≤ 40-p.all := by dsimp only [p]; omega
  have hqY : middle (regularAggregateFlag Q Finset.univ) ≤ 185-middle p := by dsimp only [p]; omega
  have hqT : total (regularAggregateFlag Q Finset.univ) ≤ 35527-total p := by dsimp only [p]; omega
  have hsum : (∑ F ∈ U, F.1.degreeOf 2) = p.all := by
    simp only [p, regularAggregateFlag, sumFlag_all, regularCumulativeFlag, originalCumulativeFlag_all]
  have hprodBox := RCN101.flag_box_to_ordinary K 24288170 131071 35527 40 (H*Q) hbox
  have hc := split_slope_charge (Finset.univ : Finset (RegularIndex H)) U
    (Finset.univ : Finset (RegularIndex Q)) (Finset.subset_univ _) (fun F => F.1) (fun F => F.1)
    H Q hH hQ (regularProduct_dvd_carrier H _) (regularProduct_dvd_carrier Q _)
    40 (foldUnit (middle p) (total p) p.all + 4502611644209)
    (foldUnit (185-middle p) (35527-total p) (40-p.all) + 4502611644209)
    (degreeOf_R_le_of_mem_box (H*Q) 24288170 131071 35527 40 hprodBox)
    (fun F => factorCharge' F.1 selected Gamma) (fun F => factorCharge' F.1 selected Delta)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 24288170 131071 35527 40 hHbox F.2
      have hd := factor_coordinates H U F hF
      exact factorCharge'_le_unit' inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (hy.trans (by decide +kernel)) (ht.trans (by decide +kernel))
        (hr.trans (by decide +kernel)) hd.1 hd.2.2 hd.2.1)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 24288170 131071 35527 40 hHbox F.2
      have hd := factor_coordinates H N F hF
      exact factorCharge'_le_unit' inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hnY) (hd.2.2.trans hnT) (hd.2.1.trans hnR))
    (fun F _ => by
      have hf := directFactor_data Q F.1 hQ 24288170 131071 35527 40 hQbox F.2
      have hd := factor_coordinates Q Finset.univ F (Finset.mem_univ _)
      exact factorCharge'_le_unit' inpQ F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hqY) (hd.2.2.trans hqT) (hd.2.1.trans hqR))
  rw [hsum] at hc
  have hp : p.all + (40-p.all) = 40 := by dsimp only [p]; omega
  calc
    _ ≤ _ := hc
    _ = p.all*foldUnit (middle p) (total p) p.all +
        (40-p.all)*foldUnit (185-middle p) (35527-total p) (40-p.all) +
          (p.all+(40-p.all))*4502611644209 := by ring
    _ = _ := by rw [hp]

end
end ProximityPrize.SubmissionLower.Lower80889.FoldBudgets

namespace ProximityPrize.SubmissionLower.Lower80889.FoldGeometry
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN140 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN267 RCN275 RCN286
  RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain Counting BoundaryTailSharedDegreeBudget FoldChain6813 FoldCounting
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldGeometry.instDecidableEqK : DecidableEq K := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldGeometry.instDecidableEqI : DecidableEq I := Classical.decEq _
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FoldGeometry.instStrongNormalizationMonoidP4 : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

theorem cover_count' (Q T : P4) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ g ∈ Gamma, specialization K (selected g) g Q = 0)
    (hTsolution : ∀ g ∈ Gamma, specialization K (selected g) g T = 0) :
    Gamma.card ≤ (∑ F : RegularIndex Q, (regularPairSeeds Q T selected Gamma F).card) +
      (∑ F : RegularIndex Q, factorCharge' F.1 selected Gamma) +
      (rfreeSeeds Q selected Gamma).card := by
  have hcover := cover_fold Q T hQ selected Gamma hQsolution hTsolution
  have hB : ((positiveRFactors Q).biUnion fun F => foldSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (foldSeeds F selected Gamma).card := Finset.card_biUnion_le
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
  have hA := Finset.card_biUnion_le (s := (Finset.univ : Finset (RegularIndex Q)))
    (t := fun F => regularPairSeeds Q T selected Gamma F)
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F => foldSeeds F selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F => foldSeeds F selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F)
    ((positiveRFactors Q).biUnion fun F => foldSeeds F selected Gamma)
  have he : (∑ F : RegularIndex Q, factorCharge' F.1 selected Gamma) =
      (∑ F ∈ positiveRFactors Q, (foldSeeds F selected Gamma).card) +
      (∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card) := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ => Iff.rfl)
      (f := fun F => factorCharge' F selected Gamma)]
    simp only [factorCharge', Finset.sum_add_distrib]
  omega

end
end ProximityPrize.SubmissionLower.Lower80889.FoldGeometry


