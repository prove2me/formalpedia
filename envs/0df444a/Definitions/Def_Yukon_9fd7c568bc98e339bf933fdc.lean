-- Prove2me | Definitions.Def_Yukon_9fd7c568bc98e339bf933fdc
-- name    : Yukon_9fd7c568bc98e339bf933fdc
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:26:55.462049+00:00
-- url     : https://prove2.me/theorems/e4c0000d-4ee2-4473-9665-68ad7e7cc75a
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberRouting6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberRouting6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberRouting6814.lean
--
--   yukon-proof-operation:foundation-direct-3bf04d37e24ce983b4e6a6676f7935b38da25d6dd2e66d50e38266e3b95c4d13
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzNkYTJmMTI0YWUyODEzZWU1OTVkYjVhMzk3NTE5ZjU1YjZmMzdhYTNlMDRkNzk3OWYzYjI3ZmMyYzhjYTkyZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTNiZjA0ZDM3ZTI0Y2U5ODNiNGU2YTY2NzZmNzkzNWIzOGRhMjVkNmRkMmU2NmQ1MGUzODI2NmUzYjk1YzRkMTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85ZmQ3YzU2OGJjOThlMzM5YmY5MzNmZGMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_d625fe39b20b33c5fb865ea0


















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.Lower80889.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FactorSwitch.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FactorSwitch.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.FactorSwitch.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Unequal-pair parameters for a regular factor and an arbitrary helper
source.  Keeping the source parameters explicit lets all external locator
profiles share one factor-switch proof. -/
def helperPair (L YS S leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181255, leftY, leftR, leftZ, YS, S, L⟩

def HelperPairGates (L YS S leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair L YS S leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

public theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

public theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

public theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- For each regular irreducible factor, either it divides an entire source
kernel or one source witness is coprime to it and supplies the unequal-pair
count. -/
theorem divisor_or_helper_count
    (D L S m YS : ℕ) (hD : 0 < D) (hDa : D ≤ m * 181255)
    (hshape : D + S ≤ 131071 * (YS + 1))
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates L YS S leftY leftR leftZ) :
    (∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        AsymmetricHelper.leftRegularCountCap (helperPair L YS S leftY leftR leftZ) := by
  classical
  by_cases hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K D 131071 L S v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K D 131071 L S :=
      reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
    have hQYS : wt residualYSWeights Q ≤ YS := by
      apply flag_box_ys_bound D 131071 L S YS (by decide) hshape Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      D 131071 L S hD).mp hQbox
    have hQY : Q.degreeOf 1 ≤ YS :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ S :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ L :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply AsymmetricHelper.regularSeeds_count_le_left_intersection
      (helperPair L YS S leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        exact Fintype.card_fin _)
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, (show (262144 - 181255 : ℕ) = 80889 by decide +kernel)] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      D 131071 L S m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hDa.trans (Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.Lower80889.FactorSwitch

namespace ProximityPrize.SubmissionLower.Lower80889.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open Lower80889.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.PowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- Lower and upper cumulative-weight bounds for one factor cell. -/
structure PowerRouteBox where
  tLo : ℕ
  tHi : ℕ
  yLo : ℕ
  yHi : ℕ
  rLo : ℕ
  rHi : ℕ
  deriving DecidableEq

/-- The unequal-pair profile charged after removing `j` copies of a factor. -/
def stagePair (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) :
    UnequalParameters :=
  helperPair (L - j * b.tLo) (YS - j * b.yLo) (S - j * b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (stagePair L YS S b j)

public theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

public theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

public theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- The generic form of `count_le_stageCost`. -/
theorem regularSeeds_count_le_stageCost
    (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (F : RegularIndex H)
    (hFY : F.1.degreeOf 1 ≤ b.yHi)
    (hFR : F.1.degreeOf 2 ≤ b.rHi)
    (hFZ : F.1.degreeOf 3 ≤ b.tHi)
    (Q : P4)
    (hQT : wt residualTotalWeights Q ≤ L - j * b.tLo)
    (hQY : wt residualYSWeights Q ≤ YS - j * b.yLo)
    (hQR : wt residualSWeights Q ≤ S - j * b.rLo)
    (hrel : IsRelPrime F.1 Q)
    (hgates : HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
      (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost L YS S b j := by
  have hQY' : Q.degreeOf 1 ≤ (stagePair L YS S b j).rightY := by
    simpa only [stagePair, helperPair] using (degreeY_le_ysWeight Q).trans hQY
  have hQR' : Q.degreeOf 2 ≤ (stagePair L YS S b j).rightR := by
    simpa only [stagePair, helperPair] using (degreeR_le_sWeight Q).trans hQR
  have hQZ : Q.degreeOf 3 ≤ (stagePair L YS S b j).rightZ := by
    simpa only [stagePair, helperPair] using (degreeZ_le_totalWeight Q).trans hQT
  obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
    hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
  have hcount := AsymmetricHelper.regularSeeds_count_le_left_intersection
    (stagePair L YS S b j) H Q F hrel 2130706433
    (by simpa only [stagePair, helperPair] using hFY)
    (by simpa only [stagePair, helperPair] using hFR)
    (by simpa only [stagePair, helperPair] using hFZ)
    hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      exact Fintype.card_fin _)
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    hdegree hagreement
    (by simpa only [stagePair, helperPair, UnequalParameters.errors,
      (show (262144 - 181255 : ℕ) = 80889 by decide +kernel)] using hno)
    hQzero
  simpa only [stageCost] using hcount

end

end ProximityPrize.SubmissionLower.Lower80889.PowerRoute

namespace ProximityPrize.SubmissionLower.Lower80889.BatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  Lower80889.FactorSwitch Lower80889.PowerRoute
  LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.BatchPowerRoute.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.BatchPowerRoute.instDecidableEqI : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.BatchPowerRoute.instCharPKOfNatNat : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The exact cell box of a regular factor.  With this box `stageCost` is the
actual unequal-pair charge after the displayed number of source quotients. -/
def exactRouteBox {H : P4} (F : RegularIndex H) : PowerRouteBox where
  tLo := wt residualTotalWeights F.1
  tHi := wt residualTotalWeights F.1
  yLo := wt residualYSWeights F.1
  yHi := wt residualYSWeights F.1
  rLo := wt residualSWeights F.1
  rHi := wt residualSWeights F.1

public theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

public theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

public theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- Multiplying the low terminal quotient by the removed batch power returns
an original source row in the derivative-contact box. -/
theorem reconstruct_mem_low_of_batch_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J : P4)
    (heq : P ^ j * J = reconstruct K D 131071 L S v.1)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) J <
      Dlow - j * wt (contactWeights 131071) P) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have hmul := wt_mul_le (contactWeights 131071) (P ^ j) J
  have hp := wt_pow_le (contactWeights 131071) P j
  omega

/-- Convert a selected batch exit into per-factor helper charges.  The
consumer retains the complementary product in every helper, so no internal
collision locus is charged. -/
theorem counts_of_batchExitStage
    (D L S m YS delta fuel : ℕ)
    (hD : 0 < D) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181255 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (A : Finset (RegularIndex H))
    (q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hproduct : ∀ v,
      reconstruct K D 131071 L S v.1 = regularProduct H A * q v)
    (hexit : HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) (regularProduct H A))
      131071 delta
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) H A q)
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgates : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let P := regularProduct H A
  change HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) P) 131071 delta
      (L - wt residualTotalWeights P) (YS - wt residualYSWeights P)
      (S - wt residualSWeights P) H A q at hexit
  obtain ⟨e, U, v, J, hUA, hv, hJ, heq, hbox, havoid⟩ := hexit
  let j := e.val + 1
  have hj : 1 ≤ j := by simp only [j]; omega
  have hjle : j ≤ fuel := by simp only [j]; omega
  have hjchar : j < 2130706433 := hjle.trans_lt hfuelChar
  have heqOriginal : P ^ j * J =
      reconstruct K D 131071 L S v.1 := by
    calc
      P ^ j * J = P * (P ^ e.val * J) := by
        simp only [j, pow_succ']
        ring
      _ = P * q v := by rw [heq]
      _ = reconstruct K D 131071 L S v.1 := (hproduct v).symm
  change J ∈ nestedCoefficientBox K
      (D - delta - wt (contactWeights 131071) P - e.val * delta -
        e.val * wt (contactWeights 131071) P) 131071
      (L - wt residualTotalWeights P - e.val * wt residualTotalWeights P)
      (YS - wt residualYSWeights P - e.val * wt residualYSWeights P)
      (S - wt residualSWeights P - e.val * wt residualSWeights P) at hbox
  have hweights := nested_mem_weights hbox hJ
  have hJT : wt residualTotalWeights J ≤
      L - j * wt residualTotalWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.1
  have hJY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.1
  have hJS : wt residualSWeights J ≤
      S - j * wt residualSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.2.1
  have hJcontact : wt (contactWeights 131071) J <
      D - j * delta - j * wt (contactWeights 131071) P := by
    have hc := hweights.2.2.2
    simp only [j, Nat.sub_sub, Nat.add_mul, one_mul] at hc ⊢
    omega
  have hlow : reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K (D - j * delta) 131071 L S :=
    reconstruct_mem_low_of_batch_power u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT : j * wt residualTotalWeights P ≤ L :=
    (Nat.mul_le_mul_right (wt residualTotalWeights P) hjle).trans hfeasible.1
  have hPY : j * wt residualYSWeights P ≤ YS :=
    (Nat.mul_le_mul_right (wt residualYSWeights P) hjle).trans hfeasible.2.1
  have hPS : j * wt residualSWeights P ≤ S :=
    (Nat.mul_le_mul_right (wt residualSWeights P) hjle).trans hfeasible.2.2
  refine ⟨U, hUA, ?_⟩
  intro F hFU
  have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFU)
  have hQbounds := liftedHelper_residual_bounds H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma QF = 0 := by
    exact batch_helper_zero_on_regularSeeds j D (D - j * delta) 131071
      L S m 181255 2130706433
      (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage := regularSeeds_count_le_stageCost L YS S
    (exactRouteBox F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
    (degreeZ_le_totalWeight F.1) QF
    (by simpa only [exactRouteBox] using hQbounds.1)
    (by simpa only [exactRouteBox] using hQbounds.2.1)
    (by simpa only [exactRouteBox] using hQbounds.2.2)
    hrel (by simpa only [exactRouteBox] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

/-! ## Contact-thinned consumer (lever S1): the band hypothesis is the thin budget. -/

theorem exists_strict_helper_split_of_batch_source_thin
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181255)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181255 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) delta
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hDlow :
          D - delta - wt (contactWeights 131071) (regularProduct H A) =
            (D - wt (contactWeights 131071) (regularProduct H A)) - delta := by
        omega
      have hsource : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (D - wt (contactWeights 131071) (regularProduct H A)) delta
          (wt (contactWeights 131071) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hbandThin.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudgetThin_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) (by decide) hDlow q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))

end

end ProximityPrize.SubmissionLower.Lower80889.BatchPowerRoute

namespace ProximityPrize.SubmissionLower.Lower80889.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80889.PowerRoute Lower80889.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000
/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50185 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50185 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50185 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance  _root_.ProximityPrize.SubmissionLower.Lower80889.Oracle.instDecidableRouteable (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def exactRouteBox (p : FlagDegree) : PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

/-- The arithmetic interface required by the algebraic source adapter.  The
stage-cost and gate checks are deliberately separate from band thresholds. -/
structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 37 → middle p ≤ 175 → total p ≤ 10714 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 37 → middle p ≤ 175 → total p ≤ 10714 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

/-- Semantic condition checked by one phase's prefix table.  At a routeable
parent, every strict nonrouteable stopping child is paid by the stored defect.
The algebraic batch engine turns precisely this condition into the phase cap.
-/
def PhaseDefectSound (previousCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p q, p.all ≤ 37 → middle p ≤ 175 → total p ≤ 10714 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric recurrence represented by a checked phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 37 → middle p ≤ 175 → total p ≤ 10714 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p

end ProximityPrize.SubmissionLower.Lower80889.Oracle

namespace ProximityPrize.SubmissionLower.Lower80889.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156
  RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance
  LocatorBatchProductRoute Lower80889.BatchPowerRoute
  Lower80889.FactorSwitch Lower80889.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.BatchPhase.instDecidableEqK : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.Lower80889.BatchPhase.instDecidableEqI : DecidableEq I := Classical.decEq I

public theorem sourceFuel_pos (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) (ht : total p ≤ s.totalCap)
    (hy : middle p ≤ s.middleCap) (hs : p.all ≤ s.slopeCap) :
    1 ≤ s.fuel p := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

public theorem sourceFuel_feasible (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.fuel p * total p ≤ s.totalCap ∧
      s.fuel p * middle p ≤ s.middleCap ∧
      s.fuel p * p.all ≤ s.slopeCap := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

public theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) :
    a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

public theorem sourceFuel_terminal (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.totalCap - s.fuel p * total p < total p ∨
      s.middleCap - s.fuel p * middle p < middle p ∨
      s.slopeCap - s.fuel p * p.all < p.all := by
  have hall : 0 < p.all := by omega
  have hmiddle : 0 < middle p := hall.trans_le (all_le_middle p)
  have htotal : 0 < total p := hmiddle.trans_le (middle_le_total p)
  unfold SourceNumbers.fuel
  by_cases hT : s.totalCap / total p ≤
      min (s.middleCap / middle p) (s.slopeCap / p.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle p ≤ s.slopeCap / p.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle p) hmiddle
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap p.all hr

/-- A numerical route for an aggregate flag supplies the strict algebraic
split required by the phase recursion. -/
theorem routeable_exists_strict_helper_split
    (sound : PhaseSourceSound) (D m : ℕ)
    (hweighted : D = m * 181255)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 37)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 175)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 10714) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        sound.potential.eval (regularCumulativeFlag H F) := by
  classical
  let p := regularAggregateFlag H A
  have hr : 1 ≤ p.all := hroute.1
  have hA : A.Nonempty := by
    by_contra hzero
    have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p, regularAggregateFlag, sumFlag] at hr
  have hfuel : 1 ≤ sound.source.fuel p :=
    sourceFuel_pos sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP := sourceFuel_feasible sound.source p hr
  have hterminalP := sourceFuel_terminal sound.source p hr
  have hfuelSlope : sound.source.fuel p ≤ sound.source.slopeCap := by
    calc
      sound.source.fuel p ≤ sound.source.slopeCap / p.all :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ sound.source.slopeCap := Nat.div_le_self _ _
  have hfuelM : sound.source.fuel p ≤ m := hfuelSlope.trans hslopeM
  have hfuelChar : sound.source.fuel p < 2130706433 :=
    hfuelM.trans_lt hmChar
  have hlowpos : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      0 < D - j * 50185 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50185 ≤
        (m - j) * 181255 + j * (131071 - 1) := by
    intro j _hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield : A.card < ENat.card K := by
    have hcard : A.card ≤ p.all := by
      calc
        A.card = ∑ F ∈ A, 1 := by simp
        _ ≤ ∑ F ∈ A, (regularCumulativeFlag H F).all :=
          Finset.sum_le_sum (fun F _ => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
        _ = p.all := by simp only [p, regularAggregateFlag, sumFlag_all]
    calc
      (A.card : ENat) ≤ (37 : ℕ) := by
        exact_mod_cast hcard.trans hnarrowS
      _ < ENat.card K := by
        rw [ENat.card_eq_coe_fintype_card, RCN183.field_cardinality]
        norm_num
  have factor_le_aggregate (F : RegularIndex H) (hFA : F ∈ A) :
      (regularCumulativeFlag H F).all ≤ p.all ∧
      middle (regularCumulativeFlag H F) ≤ middle p ∧
      total (regularCumulativeFlag H F) ≤ total p := by
    have hsub : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p, regularAggregateFlag, sumFlag, middle, total] using
      regularAggregateFlag_mono H hsub
  have factorFuel (F : RegularIndex H) (hFA : F ∈ A) (j : ℕ)
      (hj : j ≤ sound.source.fuel p) :
      j ≤ sound.source.fuel (regularCumulativeFlag H F) := by
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hFm : 1 ≤ middle (regularCumulativeFlag H F) :=
      hFr.trans (all_le_middle _)
    have hFt : 1 ≤ total (regularCumulativeFlag H F) :=
      hFm.trans (middle_le_total _)
    have hjT : j * total (regularCumulativeFlag H F) ≤
        sound.source.totalCap := by
      calc
        j * total (regularCumulativeFlag H F) ≤ j * total p :=
          Nat.mul_le_mul_left j hle.2.2
        _ ≤ sound.source.fuel p * total p :=
          Nat.mul_le_mul_right (total p) hj
        _ ≤ sound.source.totalCap := hfeasibleP.1
    have hjY : j * middle (regularCumulativeFlag H F) ≤
        sound.source.middleCap := by
      calc
        j * middle (regularCumulativeFlag H F) ≤ j * middle p :=
          Nat.mul_le_mul_left j hle.2.1
        _ ≤ sound.source.fuel p * middle p :=
          Nat.mul_le_mul_right (middle p) hj
        _ ≤ sound.source.middleCap := hfeasibleP.2.1
    have hjS : j * (regularCumulativeFlag H F).all ≤
        sound.source.slopeCap := by
      calc
        j * (regularCumulativeFlag H F).all ≤ j * p.all :=
          Nat.mul_le_mul_left j hle.1
        _ ≤ sound.source.fuel p * p.all :=
          Nat.mul_le_mul_right p.all hj
        _ ≤ sound.source.slopeCap := hfeasibleP.2.2
    unfold SourceNumbers.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      HelperPairGates
        (sound.source.totalCap - j * wt residualTotalWeights F.1)
        (sound.source.middleCap - j * wt residualYSWeights F.1)
        (sound.source.slopeCap - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageGates (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [hR, hY, hT] using hs
  have hcharge : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      Lower80889.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80889.BatchPowerRoute.exactRouteBox F) j ≤
          sound.potential.eval (regularCumulativeFlag H F) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageCost_le (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [Lower80889.BatchPowerRoute.exactRouteBox,
      Lower80889.Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181255 := hweighted.le
  have hP : regularProduct H A ≠ 0 := regularProduct_ne_zero H A
  have hcP : contactDec p ≤ wt (contactWeights 131071) (regularProduct H A) := by
    have h := LocatorArbitraryPowerAvoidance.contact_ge_ys 131071 (by decide)
      (regularProduct H A) hP
    simpa only [contactDec, p, regularAggregateFlag_middle,
      regularAggregateFlag_all] using h
  have hDcap : D - wt (contactWeights 131071) (regularProduct H A) ≤
      sound.source.contactCap p := by
    unfold SourceNumbers.contactCap
    omega
  have hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) 50185
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
      (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
      (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
      (sound.source.fuel p) < sound.source.gap := by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' : powerBandBudget 50185
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hold
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_le
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (sound.source.contactCap p) 50185 (contactDec p)
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.bandThin, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hthin
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono 131071 50185
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply exists_strict_helper_split_of_batch_source_thin D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50185 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hterminalP
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

/-! ## State-local phase semantics

The numerical receipt is indexed by the exact aggregate raw flag.  These
lemmas keep that state intact while the algebraic route repeatedly replaces a
routeable batch by a strict universal sub-batch.
-/

/-- Ambient-scoped form needed after the initial A split.  Only factors in
the A-universal set have the narrow ordinary bound. -/
def StateLocalRegularBoundOn (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K) (ambient : Finset (RegularIndex H))
    (cap : FlagDegree → ℕ) : Prop :=
  ∀ A : Finset (RegularIndex H), A ⊆ ambient →
    (regularAggregateFlag H A).all ≤ 37 →
    middle (regularAggregateFlag H A) ≤ 175 →
    total (regularAggregateFlag H A) ≤ 10714 →
    (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
      cap (regularAggregateFlag H A)

/-- Concrete kernel realization of one numerical source. -/
structure PhaseKernelRealization (sound : PhaseSourceSound)
    (u0 u1 : I → K) where
  D : ℕ
  m : ℕ
  weighted : D = m * 181255
  shape : D + sound.source.slopeCap ≤
    131071 * (sound.source.middleCap + 1)
  slope_le_m : sound.source.slopeCap ≤ m
  m_lt_char : m < 2130706433
  gap_le_finrank : sound.source.gap ≤ Module.finrank K
    (ConstraintKernel (K := K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)

/-- One source phase preserves a state-local bound according to the numeric
cap equation.  The only recursive calls are on strict factor subsets, hence
the receipt defect is queried at a strict raw-slope child of the parent. -/
theorem stateLocalRegularBoundOn_onePhase
    (sound : PhaseSourceSound) (u0 u1 : I → K)
    (kernel : PhaseKernelRealization sound u0 u1)
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80889)
    (previousCap nextCap defect : FlagDegree → ℕ)
    (hprevious : StateLocalRegularBoundOn H selected Gamma ambient previousCap)
    (hdefect : PhaseDefectSound previousCap sound.source
      sound.potential defect)
    (hcap : PhaseCapEquation previousCap nextCap sound.source
      sound.potential defect) :
    StateLocalRegularBoundOn H selected Gamma ambient nextCap := by
  classical
  intro A hAambient hs hy ht
  let p := regularAggregateFlag H A
  have hpreviousA :
      (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤ previousCap p :=
    hprevious A hAambient hs hy ht
  have hcapP := hcap p hs hy ht
  by_cases hrouteP : sound.source.Routeable p
  · have hphase :
        (∑ F ∈ A, (regularSeeds H selected Gamma F).card) ≤
          min (previousCap p)
            ((∑ F ∈ A,
              sound.potential.eval (regularCumulativeFlag H F)) + defect p) := by
      apply sum_count_le_min_previous_onePhase
        (fun F : RegularIndex H =>
          (regularSeeds H selected Gamma F).card)
        (fun F : RegularIndex H =>
          sound.potential.eval (regularCumulativeFlag H F))
        (fun B : Finset (RegularIndex H) =>
          sound.source.Routeable (regularAggregateFlag H B))
        (fun B : Finset (RegularIndex H) =>
          previousCap (regularAggregateFlag H B)) A (defect p)
      · intro B hBA
        have hmono := regularAggregateFlag_mono H hBA
        exact hprevious B (hBA.trans hAambient)
          (hmono.1.trans hs) (hmono.2.1.trans hy)
          (hmono.2.2.trans ht)
      · intro B hBA hnrouteB
        have hne : B ≠ A := by
          intro hBAeq
          subst B
          exact hnrouteB hrouteP
        have hproper : B ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hBA, hne⟩
        have hd := hdefect p (regularAggregateFlag H B) hs hy ht
          ⟨regularAggregateFlag_raw_mono H hBA,
            regularAggregateFlag_all_lt_of_ssubset H hproper⟩ hnrouteB
        rw [← sum_phasePotential_eval sound.potential H B] at hd
        exact hd
      · intro B hBA hrouteB
        have hmono := regularAggregateFlag_mono H hBA
        obtain ⟨U, hUB, hexit⟩ :=
          routeable_exists_strict_helper_split sound kernel.D kernel.m
            kernel.weighted kernel.shape kernel.slope_le_m kernel.m_lt_char
            u0 u1 H selected Gamma hdegree hagreement hno
            kernel.gap_le_finrank B hrouteB
            (hmono.1.trans hs) (hmono.2.1.trans hy)
            (hmono.2.2.trans ht)
        refine ⟨U, hUB, ?_⟩
        exact Finset.sum_le_sum (fun F hFU => hexit F hFU)
    rw [hcapP, if_pos hrouteP]
    simpa only [p, sum_phasePotential_eval] using hphase
  · rw [hcapP, if_neg hrouteP]
    exact hpreviousA

end

end ProximityPrize.SubmissionLower.Lower80889.BatchPhase


