-- Prove2me | Definitions.Def_Yukon_21acd551a6a6c6a8cdb57951
-- name    : Yukon_21acd551a6a6c6a8cdb57951
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:11:26.156701+00:00
-- url     : https://prove2.me/theorems/a5d65873-f356-4173-87cb-7f5399f7be52
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberSourceZeros6811.lean
--
--   yukon-proof-operation:foundation-direct-dfbe902495bf16ae65b274b12167fd8deea050677a0941e6efc87487dc394e09
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDNkY2U3NzE2NTcyNmM0ZjhjYWI4ZDQzZmNhZmE4OTQxNGY1YjZjMDBiZTVlOTUwOWVkMjRkY2E3MWFhNjAwOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWRmYmU5MDI0OTViZjE2YWU2NWIyNzRiMTIxNjdmZDhkZWVhMDUwNjc3YTA5NDFlNmVmYzg3NDg3ZGMzOTRlMDkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yMWFjZDU1MWE2YTZjNmE4Y2RiNTc5NTEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Source-sensitive zero counting for a moving coordinate on one prime slice.
The only cost input is the existing pure source-flag pole budget. No moving
fiber projection-degree inequality is assumed or asserted in this module.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811
open scoped BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN095 RCN136 RCN187 RCN204 RCN207 RCN257 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

public theorem pole_le_of_value_le {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : L) (b : ℤ)
    (hb : 0 ≤ b) (hx : v x ≤ WithZero.exp b) : poleOrder v x ≤ b := by
  unfold poleOrder
  apply max_le hb
  by_cases hz : v x = 0
  · simpa only [hz,WithZero.log_zero] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr hx

theorem moving_difference_pole_le {E L : Type*} [Field E] [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : E →+* L) (hc : ∀ c, v (coeff c) ≤ 1)
    (x : Fin 3 → L) (sigma : L) (Q U : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hU : PolynomialInFlag unitYZFlag U) :
    poleOrder v (coeff target - MvPolynomial.eval₂Hom coeff x Q -
      MvPolynomial.eval₂Hom coeff x U * sigma) ≤
      max (2*flagPole v x unitAllFlag)
        (flagPole v x unitYZFlag + poleOrder v sigma) := by
  let theta := max (2*flagPole v x unitAllFlag)
    (flagPole v x unitYZFlag + poleOrder v sigma)
  have htheta : 0 ≤ theta :=
    (mul_nonneg (by norm_num) (flagPole_nonneg _ _ _)).trans (le_max_left _ _)
  apply pole_le_of_value_le v _ theta htheta
  apply v.map_sub_le
  · have hv := valuation_eval_le_flag v coeff hc x (2 • unitAllFlag)
      (MvPolynomial.C target-Q) (inFlag_sub_poly (inFlag_const _ _) hQ)
    have he : flagPole v x (2 • unitAllFlag) = 2*flagPole v x unitAllFlag := by
      simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag]
      norm_num
    simp only [map_sub,MvPolynomial.eval₂Hom_C,he] at hv
    exact hv.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · have hu := valuation_eval_le_flag v coeff hc x unitYZFlag U hU
    have hs : v sigma ≤ WithZero.exp (poleOrder v sigma) :=
      WithZero.le_exp_of_log_le (le_max_right _ _)
    rw [map_mul]
    exact (mul_le_mul' hu hs).trans (by
      rw [← WithZero.exp_add]
      exact WithZero.exp_le_exp.mpr (le_max_right _ _))

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

theorem source_moving_pole_mass
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (CV : ℕ)
    (hbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((k+1 : ℕ) : ℤ) * (∑ nu ∈ W, poleOrder nu.val
      (algebraMap E (CoordinateField E C) target - coordinateEvaluation E C Q -
        coordinateEvaluation E C A * RCN064.movingRatio C
          (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))) ≤ (CV : ℤ) := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hbudget W
  simp only [SecondJetPoleScaling.pole_half _ h2] at hs
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  apply Finset.sum_le_sum
  intro nu _
  have hh := moving_difference_pole_le nu.val (algebraMap E (CoordinateField E C))
    (RCN344.constant_value_le_one E (CoordinateField E C) nu) (coordinate E C)
    (RCN064.movingRatio C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
    Q A target hQ hA
  simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hh

/-- Actual finite zero counting, not just a pole estimate. A moving equation
that is nonzero on this slice has at most CV/(k+1) regular zero points. -/
theorem finite_moving_zeros_of_source
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (hproper : movingEquation (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) Q A target ∉ C)
    (CV : ℕ)
    (hbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ)) :
    RCN271.FiniteRegularZeroSetBound C (surfaceMap phi (polyH K F))
      (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) (CV/(k+1)) := by
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  have hHne : coordinateEvaluation E C H ≠ 0 := by
    intro hz
    exact hH ((SecondJetComponentRoots.evaluation_zero_iff C _).mp hz)
  have hnorm : MvPolynomial.aeval (coordinate E C) (movingEquation H G Q A target) /
      MvPolynomial.aeval (coordinate E C) H =
      algebraMap E (CoordinateField E C) target - coordinateEvaluation E C Q -
        coordinateEvaluation E C A * RCN064.movingRatio C H G := by
    simp only [movingEquation,map_sub,map_mul,MvPolynomial.aeval_C,
      RCN064.movingRatio,coordinateEvaluation_eq_aeval] at *
    field_simp
  apply finite_regular_zero_bound_of_separator E C base H _ 1 (CV/(k+1)) hproper hH
  intro W
  have hsource := source_moving_pole_mass phi F C base P B U T s k n0
    hS hP hBU hUT hdn hB hn hF hH hlead hdiv h2 hfact Q A target hQ hA CV hbudget W
  simp only [pow_one]
  change (∑ nu ∈ W, poleOrder nu.val
    (MvPolynomial.aeval (coordinate E C) (movingEquation H G Q A target) /
      MvPolynomial.aeval (coordinate E C) H)) ≤ ((CV/(k+1) : ℕ) : ℤ)
  simp_rw [hnorm]
  rw [Int.natCast_ediv]
  apply (Int.le_ediv_iff_mul_le (by positivity : (0 : ℤ) < ((k+1 : ℕ) : ℤ))).mpr
  simpa only [H,G,mul_comm] using hsource








end
end ProximityPrize.SubmissionLower.MovingFiberSourceZeros6811


