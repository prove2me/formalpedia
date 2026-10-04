-- Prove2me | Definitions.Def_Yukon_6fa19eb79d6770597b78bb32
-- name    : Yukon_6fa19eb79d6770597b78bb32
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T20:36:56.479915+00:00
-- url     : https://prove2.me/theorems/8b773d1a-2fb4-4777-9c84-a24ee0ea15ae
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceLinearOwnerData6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-aebedc526aa68534c30dd1555d67ce84361f147da2e1c2b3d37f5072a6221c84
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiY2VlYzVhZTQ0NjQ2ZmUyMTIyMDJiNzM3OGZiYTJmNzVlNWQ3YWVkMjczOTMxNTg2NDUwYzlkZjBhYjc2MTQyNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtYWViZWRjNTI2YWE2ODUzNGMzMGRkMTU1NWQ2N2NlODQzNjFmMTQ3ZGEyZTFjMmIzZDM3ZjUwNzJhNjIyMWM4NCIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzZmYTE5ZWI3OWQ2NzcwNTk3Yjc4YmIzMiIsInYiOjJ9]

import Definitions.Def_Yukon_987f95a0aff41d97f83b5198
























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Supply the small linear-flow coefficients from the actual unique-owner
branch, rather than assuming a small rational representative. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingFiberThreeSources6811
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 MovingSourceOwnerSplit6814
open MovingSourceTwoProfiles6814 MovingSourceOwnerRouting6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814
open MovingSourceDenominatorChange6814 MovingSourceReducedTailWeights6814
open RCN234 RCN156

variable {K : Type} [Field K] [CharP K 2130706433]

theorem unique_linear_shape
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S Sz : Source F) (hS : Profile S 31 98 995 14 2 3) (hZ : Profile Sz 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P) (hs : J.degreeOf 1=1)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (huniqueS : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (huniqueZ : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J Sz.P) :
    ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331 := by
  rcases hS with ⟨hSB,hSU,hST,hSs,hSk,hSn⟩
  rcases hZ with ⟨hZB,hZU,hZT,hZs,hZk,hZn⟩
  let phi := carrierMap F
  let z := ratio phi F
  have hPs := canonical_source_power F S (by rw [hST]; omega) hpos hsmall (by rw [hSk]; omega)
  have hPz := canonical_source_power F Sz (by rw [hZT]; omega) hpos hsmall (by rw [hZk]; omega)
  have hs3 : (Polynomial.X-Polynomial.C z)^3 ∣ rootPolynomialMap phi S.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^3 ∣ (asS S.P).map (carrierMap F)
    simpa only [Source.d,hSk] using hPs.2
  have hz7 : (Polynomial.X-Polynomial.C z)^7 ∣ rootPolynomialMap phi Sz.P := by
    change (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^7 ∣ (asS Sz.P).map (carrierMap F)
    simpa only [Source.d,hZk] using hPz.2
  have hJne : rootPolynomialMap phi J≠0 := by
    intro hz
    have hd := map_dvd (rootPolynomialMap phi) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hPs.1 hd
  have hmpos : 0<(rootPolynomialMap phi J).rootMultiplicity z :=
    (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hml := Polynomial.natDegree_le_of_dvd ((rootPolynomialMap phi J).pow_rootMultiplicity_dvd z) hJne
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hml
  have hdeg : (rootPolynomialMap phi J).natDegree≤1 :=
    Polynomial.natDegree_map_le.trans_eq ((asS_natDegree J).trans hs)
  have horder : (rootPolynomialMap phi J).rootMultiplicity z≤1 := hml.trans hdeg
  have hm : (rootPolynomialMap phi J).rootMultiplicity z=1 := by omega
  obtain ⟨a,ha,haW,-⟩ := unique_owner_charges phi z S.P J (source_nonzero F S) hJ huniqueS 3 1 hJne hm hs3
  obtain ⟨b,hb,hbW,-⟩ := unique_owner_charges phi z Sz.P J (source_nonzero F Sz) hJ huniqueZ 7 1 hJne hm hz7
  simp only [mul_one] at ha hb
  have hSc := source_caps F S
  have hZc := source_caps F Sz
  rw [hSB,hSU,hST,hSs] at hSc
  rw [hZB,hZU,hZT,hZs] at hZc
  have hB : weightedTotalDegree slopeWeights J≤7 := by
    have h1 := Nat.mul_le_mul_right (weightedTotalDegree slopeWeights J) hb
    have h2 := (hbW slopeWeights).trans hZc.1
    omega
  have hU : weightedTotalDegree middleWeights J≤25 := by
    have h1 := Nat.mul_le_mul_right (weightedTotalDegree middleWeights J) hb
    have h2 := (hbW middleWeights).trans hZc.2.1
    omega
  have hT : weightedTotalDegree totalWeights J≤331 := by
    have h1 := Nat.mul_le_mul_right (weightedTotalDegree totalWeights J) ha
    have h2 := (haW totalWeights).trans hSc.2.2.1
    omega
  intro e he
  exact ⟨by simpa [weight_coords,slopeWeights,Nat.mul_comm] using
      (MvPolynomial.le_weightedTotalDegree slopeWeights he).trans hB,
    by simpa [weight_coords,middleWeights] using
      (MvPolynomial.le_weightedTotalDegree middleWeights he).trans hU,
    by simpa [weight_coords,totalWeights] using
      (MvPolynomial.le_weightedTotalDegree totalWeights he).trans hT⟩

/-- The concrete linear-owner branch supplies all coefficient caps and
the exact all-tail denominator-change identity. No count is assumed. -/
theorem linear_owner_reduced_tails
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S Sz : Source F) (hS : Profile S 31 98 995 14 2 3) (hZ : Profile Sz 53 177 3429 24 6 8)
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJ : Irreducible J) (hJS : J∣S.P) (hs : J.degreeOf 1=1)
    (hroot : rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0)
    (huniqueS : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J S.P)
    (huniqueZ : UniqueOwner (rootEvaluation (carrierMap F) (ratio (carrierMap F) F)) J Sz.P) :
    carrierMap F (linearH J)≠0 ∧
    (wt residualSWeights (linearH J)≤5 ∧ wt residualYSWeights (linearH J)≤24 ∧
      wt residualTotalWeights (linearH J)≤330) ∧
    (wt residualSWeights (linearG J)≤7 ∧ wt residualYSWeights (linearG J)≤25 ∧
      wt residualTotalWeights (linearG J)≤331) ∧
    ∀ n, (F∣(linearH J)^(2*n)*RCN313.numerator K F n-
      (RCN313.polyH K F)^(2*n)*numerators (linearH J) (linearG J) n) ∧
      wt residualSWeights (numerators (linearH J) (linearG J) n)≤11*n ∧
      wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+48*n ∧
      wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n := by
  have hshape := unique_linear_shape F S Sz hS hZ hFT hpos hsmall J hJ hJS hs hroot huniqueS huniqueZ
  have hcoeff := linear_coefficient_weights J 7 25 331 hshape
  refine ⟨linearH_nonzero_on_carrier J hJ.ne_zero hs F 331
    (fun e he => (hshape e he).2.2) (by omega),hcoeff.1,hcoeff.2,?_⟩
  intro n
  exact ⟨linear_denominator_change J hJ.ne_zero hs F hpos hsmall 331
    (fun e he => (hshape e he).2.2) (by omega) hroot n,linear_tail_weights J hshape n⟩





end
end ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814


