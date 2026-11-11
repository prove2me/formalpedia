-- Prove2me | Definitions.Def_Q223SES000
-- name    : Q223SES000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:46:26.681106+00:00
-- url     : https://prove2.me/theorems/a4ff7e66-1b8f-4031-8e6f-7e7c4ade5da0
-- title:
--   Definitions bundle Q223SES000 of the split of OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 225 declarations of OpenAI's Lean: 80 definitions, 7 instances and 138 theorems. The definitions and types are `OAI.MaximalSeshadri.AbsolutelyConvergentAt`, `OAI.MaximalSeshadri.ActualInterpolation.germCoefficients`, `OAI.MaximalSeshadri.ActualInterpolation.seriesValueMap`, `OAI.MaximalSeshadri.AdicInjective.adicTorsion`, `OAI.MaximalSeshadri.AffineBlowup.projection`, `OAI.MaximalSeshadri.AffineBlowup.scheme`, `OAI.MaximalSeshadri.AnalyticCoordinates.BiSeries`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticCoefficientLinear`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticCoefficients`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticFunctionAlgebra`, `OAI.MaximalSeshadri.AnalyticCoordinates.analyticPullback`, `OAI.MaximalSeshadri.AnalyticCoordinates.biCoeff`, `OAI.MaximalSeshadri.AnalyticCoordinates.biSeries`, `OAI.MaximalSeshadri.AnalyticCoordinates.coeffConvolution`, `OAI.MaximalSeshadri.AnalyticCoordinates.coordinateVector`, `OAI.MaximalSeshadri.AnalyticCoordinates.instHasAntidiagonalExponent`, `OAI.MaximalSeshadri.AnalyticCoordinates.ordinaryCoefficient`, `OAI.MaximalSeshadri.AnalyticCoordinates.wordExponent`, `OAI.MaximalSeshadri.BlowupLift.coefficient`, `OAI.MaximalSeshadri.ConvergentSeries`, `OAI.MaximalSeshadri.DerivativeSummable`, `OAI.MaximalSeshadri.Exponent`, `OAI.MaximalSeshadri.Geometry.IsBlowup.iso`, `OAI.MaximalSeshadri.Geometry.modulePowFrame`, `OAI.MaximalSeshadri.Geometry.modulePowMap`, `OAI.MaximalSeshadri.Geometry.modulePresheafRestrict`, `OAI.MaximalSeshadri.Geometry.modulePresheafRestrictAdjunction`, `OAI.MaximalSeshadri.Geometry.modulePresheafRestrictOpensIso`, `OAI.MaximalSeshadri.Geometry.modulePresheafTensorRestrict`, `OAI.MaximalSeshadri.Geometry.moduleSheafificationRestrict`, `OAI.MaximalSeshadri.Geometry.moduleTensorIso`, `OAI.MaximalSeshadri.Geometry.moduleTensorMap`, `OAI.MaximalSeshadri.Geometry.moduleTensorRestrict`, `OAI.MaximalSeshadri.Geometry.moduleTensorUnit`, `OAI.MaximalSeshadri.Geometry.powerSection`, `OAI.MaximalSeshadri.Geometry.unitPowerIso`, `OAI.MaximalSeshadri.IdealModule.closedInclusion`, `OAI.MaximalSeshadri.IdealModule.closedModule`, `OAI.MaximalSeshadri.IdealModule.equationToIdeal`, `OAI.MaximalSeshadri.IdealModule.fromSection` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: `Seshadri_Analytic_ConvergentSeries`, `Seshadri_Analytic_CoordinateJets`, `Seshadri_Analytic_FormalSeries`, `Seshadri_Analytic_TaylorCoefficients`, `Seshadri_Blowup_BlowupIntegral`, `Seshadri_Blowup_ExceptionalIdeal`, `Seshadri_Blowup_LocalEquations`, `Seshadri_Blowup_LocalUniversal`, `Seshadri_Blowup_PlaneCharts`, `Seshadri_Blowup_PrincipalCharts`, `Seshadri_Blowup_ReesAlgebra`, `Seshadri_Blowup_ReesCharts`, `Seshadri_Blowup_Uniqueness`, `Seshadri_Cohomology_AffineVanishing`, `Seshadri_Cohomology_Injectives`, `Seshadri_Interpolation_ActualInterpolation`, `Seshadri_Sheaves_CartierModule`, `Seshadri_Sheaves_PowerExtension`, `Seshadri_Sheaves_Restriction`.
--
--   **Imports.** It imports the published bundle `Def_MaximalSeshadriConstants`.
--
--   **Imported by** (directly, in this split): the bundles `Q223SES004` and `Q223SES005`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_ConvergentSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri
open scoped BigOperators Topology
open Filter Set

abbrev Exponent := ℕ × ℕ

noncomputable def monomialDeriv (n a : ℕ) (x : ℂ) : ℂ :=
  (n.descFactorial a : ℂ) * x ^ (n - a)

lemma monomialDeriv_eq (n a : ℕ) :
    monomialDeriv n a = iteratedDeriv a (fun x : ℂ => x ^ n) := by
  ext x
  simp only [monomialDeriv, iteratedDeriv_pow]

lemma deriv_monomialDeriv (n a : ℕ) :
    deriv (monomialDeriv n a) = monomialDeriv n (a + 1) := by
  simp only [monomialDeriv_eq, iteratedDeriv_succ]

lemma differentiable_monomialDeriv (n a : ℕ) :
    Differentiable ℂ (monomialDeriv n a) := by
  unfold monomialDeriv
  fun_prop

noncomputable def seriesPartial (c : Exponent → ℂ) (a b : ℕ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z

noncomputable def seriesEval (c : Exponent → ℂ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * x ^ p.1 * z ^ p.2

lemma seriesPartial_zero (c : Exponent → ℂ) : seriesPartial c 0 0 = seriesEval c := by
  ext x z
  simp [seriesPartial, seriesEval, monomialDeriv]

noncomputable def derivativeMajorant (c : Exponent → ℂ) (R : ℝ) (a b : ℕ)
    (p : Exponent) : ℝ :=
  ‖c p‖ * ((p.1.descFactorial a : ℝ) * R ^ (p.1 - a)) *
    ((p.2.descFactorial b : ℝ) * R ^ (p.2 - b))

def DerivativeSummable (c : Exponent → ℂ) (R : ℝ) : Prop :=
  ∀ a b : ℕ, Summable (derivativeMajorant c R a b)

lemma norm_monomialDeriv_le (n a : ℕ) (x : ℂ) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖monomialDeriv n a x‖ ≤ (n.descFactorial a : ℝ) * R ^ (n - a) := by
  simp only [monomialDeriv, norm_mul, norm_natCast, norm_pow]
  gcongr

lemma norm_seriesTerm_le (c : Exponent → ℂ) (R : ℝ) (a b : ℕ) (p : Exponent)
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    ‖c p * monomialDeriv p.1 a x * monomialDeriv p.2 b z‖ ≤
      derivativeMajorant c R a b p := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_monomialDeriv_le _ _ _ _ hx)
    (norm_nonneg _)) (norm_monomialDeriv_le _ _ _ _ hz) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      ((norm_nonneg x).trans hx) _)))

lemma deriv_seriesPartial_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ ≤ R) :
    deriv (fun w => seriesPartial c a b w z) x = seriesPartial c (a + 1) b x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a w *
      monomialDeriv p.2 b z)
    (fun p => ((differentiable_monomialDeriv p.1 a).const_mul (c p)).mul_const
      (monomialDeriv p.2 b z) |>.differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p w z
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le) hz)
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a w * monomialDeriv p.2 b z) x =
        c p * monomialDeriv p.1 (a + 1) x * monomialDeriv p.2 b z := by
    rw [deriv_mul_const_field, deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma deriv_seriesPartial_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ ≤ R) (hz : ‖z‖ < R) :
    deriv (fun w => seriesPartial c a b x w) z = seriesPartial c a (b + 1) x z := by
  have hsum := Complex.hasSum_deriv_of_summable_norm (hs a b)
    (U := Metric.ball (0 : ℂ) R)
    (F := fun p : Exponent => fun w : ℂ => c p * monomialDeriv p.1 a x *
      monomialDeriv p.2 b w)
    (fun p => ((differentiable_monomialDeriv p.2 b).const_mul
      (c p * monomialDeriv p.1 a x)).differentiableOn)
    Metric.isOpen_ball
    (fun p w hw => norm_seriesTerm_le c R a b p x w hx
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he (p : Exponent) :
      deriv (fun w : ℂ => c p * monomialDeriv p.1 a x * monomialDeriv p.2 b w) z =
        c p * monomialDeriv p.1 a x * monomialDeriv p.2 (b + 1) z := by
    rw [deriv_const_mul_field, deriv_monomialDeriv]
  simpa only [seriesPartial, he] using hsum.tsum_eq.symm

lemma iteratedDeriv_series_left (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv a (fun w => seriesEval c w z) x = seriesPartial c a 0 x z := by
  induction a generalizing x with
  | zero => simp [← seriesPartial_zero]
  | succ a ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv a (fun w => seriesEval c w z) =ᶠ[𝓝 x]
        (fun w => seriesPartial c a 0 w z) := by
      filter_upwards [((continuous_norm.tendsto x).eventually (gt_mem_nhds hx))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_left c R hs a 0 x z hx hz.le

lemma iteratedDeriv_series_right (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun w => seriesPartial c a 0 x w) z = seriesPartial c a b x z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv b (fun w => seriesPartial c a 0 x w) =ᶠ[𝓝 z]
        (fun w => seriesPartial c a b x w) := by
      filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with w hw
      exact ih w hw
    rw [he.deriv_eq]
    exact deriv_seriesPartial_right c R hs a b x z hx.le hz

theorem mixedDeriv_seriesEval (c : Exponent → ℂ) (R : ℝ)
    (hs : DerivativeSummable c R) (a b : ℕ) (x z : ℂ)
    (hx : ‖x‖ < R) (hz : ‖z‖ < R) :
    iteratedDeriv b (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) z =
      seriesPartial c a b x z := by
  have he : (fun v => iteratedDeriv a (fun u => seriesEval c u v) x) =ᶠ[𝓝 z]
      (fun v => seriesPartial c a 0 x v) := by
    filter_upwards [((continuous_norm.tendsto z).eventually (gt_mem_nhds hz))] with v hv
    exact iteratedDeriv_series_left c R hs a x v hx hv
  rw [he.iteratedDeriv_eq b]
  exact iteratedDeriv_series_right c R hs a b x z hx hz

def AbsolutelyConvergentAt (c : Exponent → ℂ) (R : ℝ) : Prop :=
  Summable (fun p : Exponent => ‖c p‖ * R ^ (p.1 + p.2))

def ConvergentSeries (c : Exponent → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R

lemma descFactorial_radius_le (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (n.descFactorial a : ℝ) * ρ ^ (n - a) ≤
      (n : ℝ) ^ a * (ρ ^ n / ρ ^ a) := by
  by_cases h : a ≤ n
  · have he : ρ ^ (n - a) = ρ ^ n / ρ ^ a := by
      apply (eq_div_iff (pow_ne_zero _ hρ.ne')).2
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [← he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow n a)
      (pow_nonneg hρ.le _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_mul]
    positivity

theorem derivativeSummable_of_absolute (c : Exponent → ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hsmall : ρ < R)
    (hc : AbsolutelyConvergentAt c R) : DerivativeSummable c ρ := by
  let C : ℝ := ∑' p : Exponent, ‖c p‖ * R ^ (p.1 + p.2)
  have hC : 0 ≤ C := tsum_nonneg (fun p => by positivity)
  have hb (p : Exponent) : ‖c p‖ ≤ C / R ^ (p.1 + p.2) := by
    apply (le_div_iff₀ (pow_pos hR _)).2
    exact hc.le_tsum p (fun p _ => by positivity)
  have ht0 : 0 ≤ ρ / R := div_nonneg hρ.le hR.le
  have ht : ‖ρ / R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (div_lt_one hR).2 hsmall
  intro a b
  have hsum := ((summable_pow_mul_geometric_of_norm_lt_one a ht).mul_of_nonneg
    (summable_pow_mul_geometric_of_norm_lt_one b ht)
    (fun n => by positivity) (fun n => by positivity)).mul_left (C / (ρ ^ a * ρ ^ b))
  refine Summable.of_nonneg_of_le (fun p => by unfold derivativeMajorant; positivity)
    (fun p => ?_) hsum
  unfold derivativeMajorant
  calc
    _ ≤ (C / R ^ (p.1 + p.2)) *
        ((p.1 : ℝ) ^ a * (ρ ^ p.1 / ρ ^ a)) *
        ((p.2 : ℝ) ^ b * (ρ ^ p.2 / ρ ^ b)) := by
      apply mul_le_mul _ (descFactorial_radius_le p.2 b ρ hρ) (by positivity) (by positivity)
      exact mul_le_mul (hb p) (descFactorial_radius_le p.1 a ρ hρ)
        (by positivity) (by positivity)
    _ = C / (ρ ^ a * ρ ^ b) *
        ((p.1 : ℝ) ^ a * (ρ / R) ^ p.1 * ((p.2 : ℝ) ^ b * (ρ / R) ^ p.2)) := by
      rw [pow_add, div_pow, div_pow]
      ring

end MaximalSeshadri


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_TaylorCoefficients
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators NNReal ENNReal

def wordExponent {n : ℕ} (w : Fin n → Bool) : ℕ × ℕ :=
  ((Finset.univ.filter (fun i => w i = false)).card,
    (Finset.univ.filter (fun i => w i = true)).card)

lemma wordExponent_degree {n : ℕ} (w : Fin n → Bool) :
    (wordExponent w).1 + (wordExponent w).2 = n := by
  simpa [wordExponent] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => w i = false))

def coordinateVector : Bool → ℂ × ℂ
  | false => (1, 0)
  | true => (0, 1)

@[simp] lemma norm_coordinateVector (b : Bool) : ‖coordinateVector b‖ = 1 := by
  cases b <;> simp [coordinateVector, Prod.norm_def]

lemma prod_coordinate_word {n : ℕ} (w : Fin n → Bool) (x z : ℂ) :
    (∏ i, if w i = false then x else z) = x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  simp [Finset.prod_ite, wordExponent]

theorem multilinear_coordinate_expansion {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ) (x z : ℂ) :
    p (fun _ => (x, z)) =
      ∑ w : Fin n → Bool,
        p (fun i => coordinateVector (w i)) *
          x ^ (wordExponent w).1 * z ^ (wordExponent w).2 := by
  have h := p.map_sum (fun (_ : Fin n) (b : Bool) =>
    (if b = false then x else z) • coordinateVector b)
  have he : (fun _ : Fin n => ∑ b : Bool,
      (if b = false then x else z) • coordinateVector b) = fun _ => (x, z) := by
    ext i <;> simp [coordinateVector]
  rw [he] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  rw [p.map_smul_univ, smul_eq_mul, prod_coordinate_word]
  ring

def ordinaryCoefficient (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) : ℂ :=
  ∑ w : Fin (a + b) → Bool, if wordExponent w = (a, b) then
    p (a + b) (fun i => coordinateVector (w i)) else 0

lemma ordinaryCoefficient_norm_le (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ ≤ (2 : ℝ) ^ (a + b) * ‖p (a + b)‖ := by
  calc
    _ ≤ ∑ _w : Fin (a + b) → Bool, ‖p (a + b)‖ := by
      apply norm_sum_le_of_le _
      intro w _
      split_ifs
      · simpa using (p (a + b)).le_opNorm (fun i => coordinateVector (w i))
      · simp
    _ = _ := by simp

lemma ordinaryCoefficient_eq_degree (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    {a b n : ℕ} (h : a + b = n) :
    ordinaryCoefficient p a b = ∑ w : Fin n → Bool, if wordExponent w = (a, b) then
      p n (fun i => coordinateVector (w i)) else 0 := by
  subst n
  rfl

theorem ordinaryCoefficient_homogeneous (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (x z : ℂ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
        p n (fun _ => (x, z)) := by
  rw [multilinear_coordinate_expansion]
  have he : (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ w : Fin n → Bool,
        if wordExponent w = ab then
          p n (fun i => coordinateVector (w i)) * x ^ ab.1 * z ^ ab.2 else 0 := by
    apply Finset.sum_congr rfl
    intro ab hab
    rw [ordinaryCoefficient_eq_degree p (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [Finset.HasAntidiagonal.mem_antidiagonal, wordExponent_degree]

theorem ordinaryCoefficient_geometric_bound (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (ρ C : ℝ) (hρ : 0 < ρ)
    (hp : ∀ n, ‖p n‖ ≤ C / ρ ^ n) (a b : ℕ) :
    ‖ordinaryCoefficient p a b‖ * (ρ / 4) ^ (a + b) ≤ C * (1 / 2 : ℝ) ^ (a + b) := by
  calc
    _ ≤ ((2 : ℝ) ^ (a + b) * (C / ρ ^ (a + b))) * (ρ / 4) ^ (a + b) := by
      gcongr
      exact (ordinaryCoefficient_norm_le p a b).trans (mul_le_mul_of_nonneg_left
        (hp (a + b)) (by positivity))
    _ = _ := by
      rw [div_pow, div_pow]
      field_simp
      ring_nf
      rw [Nat.mul_comm a 2, Nat.mul_comm b 2, pow_mul, pow_mul]
      norm_num

theorem ordinaryCoefficient_absolutely_convergent
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (ρ : ℝ≥0)
    (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < p.radius) :
    Summable (fun ab : ℕ × ℕ => ‖ordinaryCoefficient p ab.1 ab.2‖ *
      ((ρ : ℝ) / 4) ^ (ab.1 + ab.2)) := by
  obtain ⟨C, _, hp⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ hr
  have hs : Summable (fun ab : ℕ × ℕ => C * ((1 / 2 : ℝ) ^ (ab.1 + ab.2))) := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [pow_add] using (h.mul_of_nonneg h (fun _ => by positivity)
      (fun _ => by positivity)).mul_left C
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun ab => ordinaryCoefficient_geometric_bound p ρ C hρ hp ab.1 ab.2) hs

lemma ordinary_hasSum_by_degree (c : ℕ × ℕ → ℂ) (hc : Summable c) :
    HasSum (fun n : ℕ => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, c ab) (∑' ab, c ab) := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hs : HasSum (fun s : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n => c s.2.val)
      (∑' ab, c ab) := e.hasSum_iff.mpr hc.hasSum
  apply hs.sigma
  intro n
  simpa only [Finset.sum_coe_sort] using
    (hasSum_fintype (fun ab : Finset.HasAntidiagonal.antidiagonal n => c ab.val))

lemma ordinary_terms_summable (c : ℕ × ℕ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)))
    (x z : ℂ) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun ab => c ab * x ^ ab.1 * z ^ ab.2) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hc
  intro ab
  simp only [norm_mul, norm_pow, pow_add, ← mul_assoc]
  gcongr

theorem hasFPowerSeriesOnBall_ordinary_expansion
    (f : ℂ × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (r : ℝ≥0∞) (hf : HasFPowerSeriesOnBall f p 0 r)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hr : (ρ : ℝ≥0∞) < r)
    (x z : ℂ) (hx : ‖x‖ < (ρ : ℝ) / 4) (hz : ‖z‖ < (ρ : ℝ) / 4) :
    f (x,z) = ∑' ab : ℕ × ℕ, ordinaryCoefficient p ab.1 ab.2 * x ^ ab.1 * z ^ ab.2 := by
  have hc := ordinaryCoefficient_absolutely_convergent p ρ hρ (hr.trans_le hf.r_le)
  have hs := ordinary_terms_summable (fun ab => ordinaryCoefficient p ab.1 ab.2)
    ((ρ : ℝ) / 4) (by positivity) hc x z hx.le hz.le
  have hh := ordinary_hasSum_by_degree _ hs
  simp_rw [ordinaryCoefficient_homogeneous] at hh
  have hnorm : ‖(x,z)‖₊ < ρ := by
    change max ‖x‖ ‖z‖ < (ρ : ℝ)
    apply max_lt
    · linarith [show (0 : ℝ) < ρ from hρ]
    · linarith [show (0 : ℝ) < ρ from hρ]
  have hm : (x,z) ∈ Metric.eball (0 : ℂ × ℂ) r := by
    rw [mem_eball_zero_iff]
    exact (ENNReal.coe_lt_coe.mpr hnorm).trans hr
  have hh' := hf.hasSum hm
  simpa only [zero_add] using hh'.unique hh

theorem analyticAt_exists_ordinary_expansion (f : ℂ × ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ∃ c : ℕ × ℕ → ℂ, ∃ R : ℝ, 0 < R ∧
      Summable (fun ab => ‖c ab‖ * R ^ (ab.1 + ab.2)) ∧
      ∀ x z : ℂ, ‖x‖ < R → ‖z‖ < R →
        f (x,z) = ∑' ab : ℕ × ℕ, c ab * x ^ ab.1 * z ^ ab.2 := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hρ' : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ
  refine ⟨fun ab => ordinaryCoefficient p ab.1 ab.2, (ρ : ℝ) / 4, by positivity,
    ordinaryCoefficient_absolutely_convergent p ρ hρ' (hr.trans_le hp.r_le), ?_⟩
  intro x z hx hz
  exact hasFPowerSeriesOnBall_ordinary_expansion f p r hp ρ hρ' hr x z hx hz

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter Set

lemma monomialDeriv_at_zero (n a : ℕ) :
    monomialDeriv n a 0 = if n = a then (a.factorial : ℂ) else 0 := by
  by_cases h : n = a
  · subst n
    simp [monomialDeriv, Nat.descFactorial_self]
  · rw [ite_eq_right_iff.mpr (fun he => (h he).elim)]
    by_cases hn : n < a
    · simp [monomialDeriv, Nat.descFactorial_eq_zero_iff_lt.mpr hn]
    · have hd : n - a ≠ 0 := by omega
      simp [monomialDeriv, zero_pow hd]

lemma seriesPartial_at_zero (c : Exponent → ℂ) (a b : ℕ) :
    seriesPartial c a b 0 0 = c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  unfold seriesPartial
  rw [tsum_eq_single (a,b)]
  · simp [monomialDeriv_at_zero]
  · intro p hp
    by_cases h₁ : p.1 = a
    · have h₂ : p.2 ≠ b := by intro h₂; exact hp (Prod.ext h₁ h₂)
      simp [monomialDeriv_at_zero, h₂]
    · simp [monomialDeriv_at_zero, h₁]

theorem mixedDeriv_at_zero (c : Exponent → ℂ) (hc : ConvergentSeries c) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => seriesEval c x z) 0) 0 =
      c (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) := by
  obtain ⟨R, hR, hconv⟩ := hc
  rw [mixedDeriv_seriesEval c (R / 2)
    (derivativeSummable_of_absolute c R (R / 2) hR (by positivity) (by linarith) hconv)
    a b 0 0 (by simpa using (show (0 : ℝ) < R / 2 by positivity))
      (by simpa using (show (0 : ℝ) < R / 2 by positivity))]
  exact seriesPartial_at_zero c a b

lemma mixedDeriv_congr_germ (f g : ℂ × ℂ → ℂ) (h : f =ᶠ[𝓝 0] g) (a b : ℕ) :
    iteratedDeriv b (fun z => iteratedDeriv a (fun x => f (x,z)) 0) 0 =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => g (x,z)) 0) 0 := by
  obtain ⟨ε, hε, hfg⟩ := Metric.eventually_nhds_iff.mp h
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < ε := by
    change {z : ℂ | ‖z‖ < ε} ∈ 𝓝 (0 : ℂ)
    simpa only [Metric.ball, dist_zero_right] using
      (Metric.ball_mem_nhds (0 : ℂ) hε)
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with z hz
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hn] with x hx
  apply hfg
  simpa [Prod.dist_eq, dist_zero_right, max_lt_iff] using And.intro hx hz

theorem convergent_expansion_unique (c d : Exponent → ℂ)
    (hc : ConvergentSeries c) (hd : ConvergentSeries d)
    (heq : (fun q : ℂ × ℂ => seriesEval c q.1 q.2) =ᶠ[𝓝 0]
      (fun q : ℂ × ℂ => seriesEval d q.1 q.2)) : c = d := by
  ext ab
  have h := mixedDeriv_congr_germ _ _ heq ab.1 ab.2
  rw [mixedDeriv_at_zero c hc, mixedDeriv_at_zero d hd] at h
  exact mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.1)
    (mul_right_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero ab.2) h)

def analyticFunctionAlgebra : Subalgebra ℂ (ℂ × ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' := fun hf hg => hf.mul hg
  add_mem' := fun hf hg => hf.add hg
  algebraMap_mem' := fun _ => analyticAt_const

def analyticCoefficients (f : analyticFunctionAlgebra) : Exponent → ℂ :=
  (analyticAt_exists_ordinary_expansion f f.property).choose

lemma analyticCoefficients_spec (f : analyticFunctionAlgebra) :
    ConvergentSeries (analyticCoefficients f) ∧
      (fun q : ℂ × ℂ => f.val q) =ᶠ[𝓝 0]
        (fun q : ℂ × ℂ => seriesEval (analyticCoefficients f) q.1 q.2) := by
  obtain ⟨R, hR, hsum, heq⟩ := (analyticAt_exists_ordinary_expansion f f.property).choose_spec
  refine ⟨⟨R, hR, hsum⟩, ?_⟩
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hq' : ‖q.1‖ < R ∧ ‖q.2‖ < R := by
    simpa [Prod.dist_eq, dist_zero_right, Prod.norm_def, max_lt_iff] using hq
  exact heq q.1 q.2 hq'.1 hq'.2

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance instHasAntidiagonalExponent : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

def coeffConvolution (c d : Exponent → ℂ) (e : Exponent) : ℂ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, c ab.1 * d ab.2

lemma absolute_mono {c : Exponent → ℂ} {R ρ : ℝ}
    (hR : AbsolutelyConvergentAt c R) (hρ : 0 ≤ ρ) (h : ρ ≤ R) :
    AbsolutelyConvergentAt c ρ := by
  exact Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h _) (norm_nonneg _)) hR

lemma absolute_terms_summable {c : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    Summable (fun e : Exponent => ‖c e * x ^ e.1 * z ^ e.2‖) := by
  exact (ordinary_terms_summable c R ((norm_nonneg _).trans hx) hc x z hx hz).norm

lemma absolute_convolution {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (coeffConvolution c d) R := by
  have hs := hc.mul_of_nonneg hd (fun e => by positivity) (fun e => by positivity)
  have ht := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
    (A := Exponent)).summable_iff.mpr hs
  have hu := ht.sigma
  change Summable (fun e : Exponent => ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.val.1‖ * R ^ (ab.val.1.1 + ab.val.1.2)) *
      (‖d ab.val.2‖ * R ^ (ab.val.2.1 + ab.val.2.2))) at hu
  have hu' : Summable (fun e : Exponent => ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
    (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
      (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))) := hu.congr (fun e => by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
          (fun ab : Exponent × Exponent => (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
            (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2))))
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) hu'
  calc
    ‖coeffConvolution c d e‖ * R ^ (e.1 + e.2) ≤
      (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e, ‖c ab.1 * d ab.2‖) *
        R ^ (e.1 + e.2) := by
          exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hR _)
    _ = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal e,
      (‖c ab.1‖ * R ^ (ab.1.1 + ab.1.2)) *
        (‖d ab.2‖ * R ^ (ab.2.1 + ab.2.2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ab hab
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have he₁ := congrArg Prod.fst he
      have he₂ := congrArg Prod.snd he
      simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
      rw [← he₁, ← he₂, norm_mul]
      simp only [pow_add]
      ring

lemma seriesEval_convolution {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (coeffConvolution c d) x z = seriesEval c x z * seriesEval d x z := by
  have hf := absolute_terms_summable hc hx hz
  have hg := absolute_terms_summable hd hx hz
  have hs := summable_mul_of_summable_norm hf hg
  let E := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := Exponent)
  have ht := E.summable_iff.mpr hs
  unfold seriesEval
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← E.tsum_eq]
  have hsum := ht.tsum_sigma
  simp only [Function.comp_def] at hsum
  rw [hsum]
  apply tsum_congr
  intro e
  change _ = ∑' ab : Finset.HasAntidiagonal.antidiagonal e,
    (c ab.val.1 * x ^ ab.val.1.1 * z ^ ab.val.1.2) *
      (d ab.val.2 * x ^ ab.val.2.1 * z ^ ab.val.2.2)
  rw [tsum_fintype]
  have heq := Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal e)
    (fun ab : Exponent × Exponent =>
      (c ab.1 * x ^ ab.1.1 * z ^ ab.1.2) * (d ab.2 * x ^ ab.2.1 * z ^ ab.2.2))
  rw [heq]
  simp only [coeffConvolution, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  simp only [Prod.fst_add, Prod.snd_add] at he₁ he₂
  rw [← he₁, ← he₂]
  simp only [pow_add]
  ring

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_FormalSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance instHasAntidiagonalExponent_1_r71b9e0_1 : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite
lemma absolute_add {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (c + d) R := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hc.add hd)
  change ‖c p + d p‖ * R ^ (p.1 + p.2) ≤ _
  calc
    _ ≤ (‖c p‖ + ‖d p‖) * R ^ (p.1 + p.2) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hR _)
    _ = _ := by ring

lemma seriesEval_add {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (c + d) x z = seriesEval c x z + seriesEval d x z := by
  simp only [seriesEval, Pi.add_apply, add_mul]
  exact (absolute_terms_summable hc hx hz).of_norm.tsum_add
    (absolute_terms_summable hd hx hz).of_norm

lemma eventually_polydisk {R : ℝ} (hR : 0 < R) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖q.1‖ < R ∧ ‖q.2‖ < R := by
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, fun q hq => ?_⟩
  simpa only [dist_zero_right, Prod.norm_def, max_lt_iff] using hq

lemma common_absolute_radius {c d : Exponent → ℂ}
    (hc : ConvergentSeries c) (hd : ConvergentSeries d) :
    ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R ∧ AbsolutelyConvergentAt d R := by
  obtain ⟨R, hR, hc⟩ := hc
  obtain ⟨S, hS, hd⟩ := hd
  refine ⟨min R S, lt_min hR hS, ?_, ?_⟩
  · exact absolute_mono hc (le_min hR.le hS.le) (min_le_left _ _)
  · exact absolute_mono hd (le_min hR.le hS.le) (min_le_right _ _)

lemma analyticCoefficients_add (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f + g) = analyticCoefficients f + analyticCoefficients g := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f + g)).1
    ⟨R, hR, absolute_add hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f + g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_add hf hg hq.1.le hq.2.le]
  change f.val q + g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_mul (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f * g) = coeffConvolution (analyticCoefficients f)
      (analyticCoefficients g) := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f * g)).1
    ⟨R, hR, absolute_convolution hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f * g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_convolution hf hg hq.1.le hq.2.le]
  change f.val q * g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_const (a : ℂ) :
    analyticCoefficients (algebraMap ℂ analyticFunctionAlgebra a) =
      fun e => if e = (0,0) then a else 0 := by
  let c : Exponent → ℂ := fun e => if e = (0,0) then a else 0
  have hc : ConvergentSeries c := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, c, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq (0,0) ‖a‖).summable
  have he (x z : ℂ) : seriesEval c x z = a := by
    simp [seriesEval, c, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec _).1 hc
  filter_upwards [(analyticCoefficients_spec (algebraMap ℂ analyticFunctionAlgebra a)).2]
    with q hq
  rw [← hq, he]
  rfl

def analyticCoefficientLinear : analyticFunctionAlgebra →ₗ[ℂ] (Exponent → ℂ) where
  toFun := analyticCoefficients
  map_add' := analyticCoefficients_add
  map_smul' a f := by
    have h := analyticCoefficients_mul (algebraMap ℂ analyticFunctionAlgebra a) f
    rw [Algebra.smul_def, h, analyticCoefficients_const]
    ext e
    simp only [coeffConvolution, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (0,e)]
    · simp [show (0 : Exponent) = (0,0) from rfl]
    · intro ab hab hne
      have ha : ab.1 ≠ 0 := by
        intro hh
        have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
        simp only [hh, zero_add] at hx
        exact hne (Prod.ext hh hx)
      have ha' : ab.1 ≠ (0,0) := ha
      simp [ha']
    · simp

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

abbrev BiSeries := PowerSeries (PowerSeries ℂ)

local instance instHasAntidiagonalExponent_2_r71b9e0_1 : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite
def biCoeff (f : BiSeries) (e : Exponent) : ℂ := coeff e.1 (coeff e.2 f)

def biSeries (c : Exponent → ℂ) : BiSeries :=
  PowerSeries.mk (fun b => PowerSeries.mk (fun a => c (a,b)))

@[simp] lemma biCoeff_biSeries (c : Exponent → ℂ) (e : Exponent) :
    biCoeff (biSeries c) e = c e := by simp [biCoeff, biSeries]

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_Injectives
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.AdicInjective
noncomputable section
universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

def adicTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

lemma torsion_mono : Monotone (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) :=
  fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab I

lemma mem_adicTorsion (x : M) : x ∈ adicTorsion I M ↔
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  rw [adicTorsion, Submodule.mem_iSup_of_directed _ (torsion_mono I M).directed_le]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

lemma fg_uniform_exponent (N : Submodule R M) (hN : N.FG)
    (h : N ≤ adicTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  classical
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    ((Submodule.fg_iff_compact N).mp hN)
    (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) h
  refine ⟨s.sup id, hs.trans (iSup_le fun n => iSup_le fun hn => ?_)⟩
  exact torsion_mono I M (Finset.le_sup (f := id) hn)

lemma exists_power_inf_le [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    ∃ m : ℕ, I ^ m ⊓ J ≤ I ^ n * J := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  refine ⟨k+n, ?_⟩
  have h := hk (k+n) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  rw [h]
  exact Ideal.mul_mono le_rfl inf_le_right

theorem adicTorsion_injective [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R M] : Module.Injective R (adicTorsion I M) := by
  apply Module.Baer.injective
  intro J g
  let g₀ : J →ₗ[R] M := (adicTorsion I M).subtype.comp g
  have hg₀ : g₀.range ≤ adicTorsion I M := by
    rintro x ⟨y, rfl⟩
    exact (g y).property
  obtain ⟨n, hn⟩ := fg_uniform_exponent I M g₀.range (Submodule.fg_range g₀) hg₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M J R
    J.subtype Subtype.val_injective g₀
  have hj : ∀ x : J, h x = g₀ x := fun x => LinearMap.congr_fun hh x
  have hzero : I ^ n * J ≤ h.ker := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change h (a * b) = 0
    rw [← smul_eq_mul, h.map_smul, hj ⟨b, hb⟩]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn (LinearMap.mem_range_self g₀ ⟨b,hb⟩)) ⟨a,ha⟩
  obtain ⟨m, hm⟩ := exists_power_inf_le I J n
  let f : R →ₗ.[R] M := ⟨J, g₀⟩
  let z : R →ₗ.[R] M := ⟨I ^ m, 0⟩
  have hz : ∀ (x : f.domain) (y : z.domain), (x : R) = y → f x = z y := by
    intro x y hxy
    change g₀ x = 0
    rw [← hj x]
    exact hzero (hm ⟨hxy ▸ y.property, x.property⟩)
  let F := f.sup z hz
  obtain ⟨H, hH⟩ := Module.Injective.extension_property R M F.domain R
    F.domain.subtype Subtype.val_injective F.toFun
  have HF : ∀ x : F.domain, H x = F x := fun x => LinearMap.congr_fun hH x
  have HJ : ∀ x : J, H x = g₀ x := by
    intro x
    rw [HF ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩]
    exact ((f.left_le_sup z hz).2 (x := x) (y := ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩) rfl).symm
  have HI : ∀ a ∈ I ^ m, H a = 0 := by
    intro a ha
    rw [HF ⟨a, (show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩]
    exact ((f.right_le_sup z hz).2 (x := ⟨a,ha⟩) (y := ⟨a,(show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩) rfl).symm
  have Hmem : ∀ a, H a ∈ adicTorsion I M := by
    intro a
    apply (mem_adicTorsion I M _).mpr
    refine ⟨m, fun b hb => ?_⟩
    rw [← H.map_smul]
    exact HI (b * a) ((I ^ m).mul_mem_right a hb)
  refine ⟨H.codRestrict (adicTorsion I M) Hmem, ?_⟩
  intro x hx
  apply Subtype.ext
  exact HJ ⟨x,hx⟩

end
end MaximalSeshadri.AdicInjective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_AffineVanishing
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.RestrictionExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_mono {M N : Y.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor f).map g) := by
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map g))
  exact PresheafOfModules.injective_of_mono g.val (op (f ''ᵁ U.unop))

end
end MaximalSeshadri.RestrictionExact


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.IdealModule
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureMap : unit Y ⟶
    (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] lemma structureMap_app (U : Y.Opens) (x : Γ(Y, U)) :
    ((structureMap f).val.app (op U)) x = (f.app U) x := rfl

def idealModule : Y.Modules := kernel (structureMap f)

def inclusion : idealModule f ⟶ unit Y :=
  kernel.ι (structureMap f)

instance instMonoModulesInclusion : Mono (inclusion f) := inferInstanceAs (Mono (kernel.ι (structureMap f)))

def sectionsKernelIso (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≅
      ModuleCat.of (Y.ringCatSheaf.obj.obj (op U))
        ((structureMap f).val.app (op U)).hom.ker :=
  PreservesKernel.iso
    (Scheme.Modules.toPresheafOfModules Y ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)) (structureMap f) ≪≫
    ModuleCat.kernelIsoKer _

lemma sectionsKernelIso_inclusion (U : Y.Opens) :
    (sectionsKernelIso f U).hom ≫
      ModuleCat.ofHom ((structureMap f).val.app (op U)).hom.ker.subtype =
        (inclusion f).val.app (op U) := by
  let E := Scheme.Modules.toPresheafOfModules Y ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)
  change ((PreservesKernel.iso E (structureMap f)).hom ≫
    (ModuleCat.kernelIsoKer (E.map (structureMap f))).hom) ≫
      ModuleCat.ofHom (E.map (structureMap f)).hom.ker.subtype =
        E.map (kernel.ι (structureMap f))
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

lemma image_eq_kernel (U : Y.Opens) :
    ((inclusion f).val.app (op U)).hom.range = RingHom.ker (f.app U).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (f.app U) (((inclusion f).val.app (op U)) y) = 0
    have h := congrArg (fun g => (g.val.app (op U)) y)
      (kernel.condition (structureMap f))
    exact h
  · intro hx
    let y : ((structureMap f).val.app (op U)).hom.ker := ⟨x, hx⟩
    refine ⟨(sectionsKernelIso f U).inv y, ?_⟩
    have h := congrArg (fun g => g ((sectionsKernelIso f U).inv y))
      (sectionsKernelIso_inclusion f U)
    simpa using h.symm

lemma image_eq_ideal [QuasiCompact f] (U : Y.affineOpens) :
    ((inclusion f).val.app (op U.1)).hom.range = f.ker.ideal U := by
  rw [image_eq_kernel, Scheme.Hom.ker_apply]

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def closedModule (I : X.IdealSheafData) : X.Modules := idealModule I.subschemeι

def closedInclusion (I : X.IdealSheafData) : closedModule I ⟶ unit X :=
  inclusion I.subschemeι

lemma closed_image (I : X.IdealSheafData) (U : X.affineOpens) :
    ((closedInclusion I).val.app (op U.1)).hom.range = I.ideal U := by
  exact (image_eq_ideal I.subschemeι U).trans (congrArg (fun J => J.ideal U) I.ker_subschemeι)

lemma isIso_of_affine_app {M N : X.Modules} (g : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso (g.app U.1)) : IsIso g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hb : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => U.val) := by
    simpa using X.isBasis_affineOpens
  have hg : IsIso (F.map g) := TopCat.Sheaf.isIso_iff_isIso_basis hb h
  let : IsIso ((Scheme.Modules.toPresheaf X).map g) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ AddCommGrpCat).map (F.map g)))
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf X)

def multiply (r : Γ(X, ⊤)) : unit X ⟶ unit X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma multiply_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (multiply r).val.app (op U) a = X.presheaf.map (homOfLE le_top).op r * a := rfl

lemma multiply_structure_zero (f : Y ⟶ X) (r : Γ(X, ⊤))
    (hr : (f.app ⊤) r = 0) : multiply r ≫ structureMap f = 0 := by
  ext U a
  change Γ(X, U) at a
  change (f.app U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) *
    (a : Γ(X, U))) = 0
  rw [map_mul]
  have he : (f.app U) (X.presheaf.map (homOfLE le_top).op r) = 0 := by
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, hr, map_zero]
  rw [he, zero_mul]

def equationToIdeal (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    unit X ⟶ idealModule f :=
  kernel.lift (structureMap f) (multiply r) (multiply_structure_zero f r hr)

@[reassoc (attr := simp)] lemma equationToIdeal_inclusion
    (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    equationToIdeal f r hr ≫ inclusion f = multiply r := kernel.lift_ι _ _ _

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

def sectionFamily {M : X.Modules} (s : Γ(M, ⊤)) : M.sections where
  val U := M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  property {U V} i := by
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) s = _
    rw [← Functor.map_comp]
    rfl

def fromSection {M : X.Modules} (s : Γ(M, ⊤)) : unit X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily s)

@[simp] lemma fromSection_app {M : X.Modules} (s : Γ(M, ⊤))
    (U : X.Opens) (a : Γ(X, U)) :
    (fromSection s).val.app (op U) a = a • M.presheaf.map (homOfLE le_top).op s := rfl

lemma fromSection_inclusion_app {M : X.Modules} (g : M ⟶ unit X)
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) ((fromSection s).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a := by
  rw [fromSection_app]
  have hn := PresheafOfModules.naturality_apply g.val (homOfLE (show U ≤ ⊤ from le_top)).op s
  change g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s) =
    X.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) s) at hn
  have he := ((g.val.app (op U)).hom).map_smul a (M.presheaf.map (homOfLE le_top).op s)
  change _ = a * (show Γ(X, U) from g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s)) at he
  exact he.trans ((congrArg (fun value : Γ(X, U) => a * value)
    (hn.trans (congrArg (X.presheaf.map (homOfLE le_top).op) hs))).trans (mul_comm _ _))

lemma isIso_fromSection {M : X.Modules} (g : M ⟶ unit X) [Mono g]
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (hprincipal : ∀ U : X.affineOpens,
      (g.val.app (op U.1)).hom.range = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (fromSection s) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective (g.val.app (op U.1)) := by
    let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
    exact PresheafOfModules.injective_of_mono g.val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg (g.val.app (op U.1)) hab
    change g.val.app (op U.1) ((fromSection s).val.app (op U.1) a) =
      g.val.app (op U.1) ((fromSection s).val.app (op U.1) b) at he
    exact (fromSection_inclusion_app g s r hs U.1 a).symm.trans
      (he.trans (fromSection_inclusion_app g s r hs U.1 b))
  · intro y
    have hy : (show Γ(X, U.1) from g.val.app (op U.1) y) ∈
        Ideal.span {X.presheaf.map (homOfLE le_top).op r} := by
      rw [← hprincipal U]
      exact ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨a, hinj ?_⟩
    exact (fromSection_inclusion_app g s r hs U.1 a).trans ha.symm

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (f r) := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : IsSMulRegular S r := Module.Flat.isSMulRegular_of_isRegular
    ⟨hr, hr.right_of_commute (fun a => mul_comm r a)⟩
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hh

lemma restriction_regular [IsAffine X] (r : Γ(X, ⊤)) (hr : IsLeftRegular r)
    (U : X.affineOpens) :
    IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r) := by
  apply regular_map_flat _ _ hr
  simpa [Scheme.Hom.appLE] using
    Scheme.Hom.flat_appLE (𝟙 X) (isAffineOpen_top X) U.2 (show U.1 ≤ (𝟙 X) ⁻¹ᵁ ⊤ from le_top)

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    MaximalSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  let unitIso : (unit Y).restrict f ≅ unit X := Scheme.Modules.restrictUnitIso f
  exact mono_comp ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) unitIso.hom

lemma restrictedInclusion_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ((closedModule I).restrict f, U)) :
    (restrictedInclusion I f).val.app (op U) s =
      (f.appIso U).hom ((closedInclusion I).val.app (op (f ''ᵁ U)) s) := rfl

lemma restricted_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    ((restrictedInclusion I f).val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  rw [I.ideal_comap_of_isOpenImmersion f U]
  ext r
  change Γ(X, U.1) at r
  change (∃ s, (restrictedInclusion I f).val.app (op U.1) s = r) ↔
    (f.appIso U.1).inv r ∈ I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  refine Iff.trans ?_ (Iff.of_eq (congrArg
    (fun ideal : Ideal Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).inv r ∈ ideal)
    (closed_image I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩)))
  change (∃ s, _) ↔ ∃ s, (closedInclusion I).val.app (op (f ''ᵁ U.1)) s = (f.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (congrArg (fun k : Γ(Y, f ''ᵁ U.1) ⟶ Γ(Y, f ''ᵁ U.1) => k ((closedInclusion I).val.app (op (f ''ᵁ U.1)) s))
      (f.appIso U.1).hom_inv_id).symm.trans
        (congrArg (f.appIso U.1).inv ((restrictedInclusion_app I f U.1 s).symm.trans hs))
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (restrictedInclusion_app I f U.1 s).trans
      ((congrArg (f.appIso U.1).hom hs).trans
        (congrArg (fun k : Γ(X, U.1) ⟶ Γ(X, U.1) => k r) (f.appIso U.1).inv_hom_id))

lemma frame_restriction (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [IsAffine X] (r : Γ(X, ⊤))
    (hprincipal : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    Nonempty ((closedModule I).restrict f ≅ unit X) := by
  have hr' : r ∈ (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [hprincipal]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hr : r ∈ ((restrictedInclusion I f).val.app (op ⊤)).hom.range := by
    rw [restricted_image I f ⟨⊤, isAffineOpen_top X⟩]
    exact hr'
  obtain ⟨s, hs⟩ := hr
  have hi : IsIso (fromSection (M := (closedModule I).restrict f) s) := isIso_fromSection (restrictedInclusion I f) s r hs
    (fun U => ?_) (restriction_regular r hregular)
  · exact ⟨(asIso (fromSection (M := (closedModule I).restrict f) s)).symm⟩
  · rw [restricted_image I f U, ← (I.comap f).map_ideal (U := U)
      (V := ⟨⊤, isAffineOpen_top X⟩) (by change U.1 ≤ ⊤; exact le_top), hprincipal]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl

end

end MaximalSeshadri.IdealModule

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

lemma map_top (J : X.IdealSheafData) (f : X ⟶ Y) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom :=
  J.ideal_map f ⟨⊤, isAffineOpen_top Y⟩ (isAffineOpen_top X)

lemma comap_top (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  apply le_antisymm
  · let J : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
    have h : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [map_top]
      simpa [J] using Ideal.le_comap_map
    have hh := (Scheme.IdealSheafData.le_map_iff_comap_le.mp h) ⟨⊤, isAffineOpen_top X⟩
    simpa [J] using hh
  · rw [Ideal.map_le_iff_le_comap]
    have h := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
    rwa [map_top] at h

end

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specIdeal (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] lemma specIdeal_top (I : Ideal R) :
    (specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdeal]

end

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

lemma comap_ι_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [I.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (I.map_ideal (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩)
    (V := U) (show U.1.ι ''ᵁ ⊤ ≤ U.1 from U.1.ι_image_top.le)).symm

lemma comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V.1 U.1 e).hom := by
  suffices hh : ((I.comap f).ideal U).map U.1.topIso.inv.hom =
      ((I.ideal V).map (f.appLE V.1 U.1 e).hom).map U.1.topIso.inv.hom by
    have hh' := congrArg (Ideal.map U.1.topIso.hom.hom) hh
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id, CommRingCat.hom_id,
      Ideal.map_id] using hh'
  rw [← comap_ι_top, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.Hom.resLE_comp_ι f e, Scheme.IdealSheafData.comap_comp,
    comap_top, comap_ι_top, Ideal.map_map, Ideal.map_map]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.hom_comp,
    Iso.inv_hom_id_assoc]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}
lemma invertible_of_local_equations
    (hf : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      obtain ⟨U, hyU, r, hr, hIr⟩ := hf y
      exact ⟨U.1, hyU, IdealModule.frame_restriction (I.comap f) U.1.ι r hIr hr.1⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end

end MaximalSeshadri.InvertibleLocal
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_CoordinateJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def analyticPullback (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : S →ₐ[ℂ] analyticFunctionAlgebra where
  toFun s := ⟨fun z => q z s, hq s⟩
  map_one' := Subtype.ext (funext fun z => (q z).map_one)
  map_mul' s t := Subtype.ext (funext fun z => (q z).map_mul s t)
  map_zero' := Subtype.ext (funext fun z => (q z).map_zero)
  map_add' s t := Subtype.ext (funext fun z => (q z).map_add s t)
  commutes' c := Subtype.ext (funext fun z => (q z).commutes c)

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def piece (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | (p : R[X]) = monomial n ((p : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change (p : R[X]) + q = monomial n (((p : R[X]) + q).coeff n)
    rw [coeff_add, map_add, ← hp, ← hq]
  smul_mem' a p hp := by
    change a • (p : R[X]) = monomial n ((a • (p : R[X])).coeff n)
    rw [coeff_smul, map_smul, ← hp]

lemma mem_piece (n : ℕ) (p : reesAlgebra I) :
    p ∈ piece I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := Iff.rfl

def component (n : ℕ) (p : reesAlgebra I) : piece I n :=
  ⟨⟨monomial n ((p : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
    by simp [mem_piece]⟩

@[simp] lemma component_val (n : ℕ) (p : reesAlgebra I) :
    ((component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

def components (p : reesAlgebra I) : ⨁ n, piece I n :=
  ⟨fun n => component I n p,
    Trunc.mk ⟨(p : R[X]).support.val, fun n => by
      classical
      by_cases hn : n ∈ (p : R[X]).support
      · exact Or.inl hn
      · right
        apply Subtype.ext
        apply Subtype.ext
        have hc : (p : R[X]).coeff n = 0 := notMem_support_iff.mp hn
        simp [component_val, hc]⟩⟩

@[simp] lemma components_apply (p : reesAlgebra I) (n : ℕ) :
    components I p n = component I n p := rfl

def componentsAdd : reesAlgebra I →+ ⨁ n, piece I n where
  toFun := components I
  map_zero' := by ext n : 1; apply Subtype.ext; apply Subtype.ext; simp [component_val]
  map_add' p q := by
    ext n : 1
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (((p : R[X]) + q).coeff n) =
      monomial n ((p : R[X]).coeff n) + monomial n ((q : R[X]).coeff n)
    rw [coeff_add, map_add]

lemma piece_coeff_ne {n m : ℕ} (hnm : n ≠ m) (p : piece I n) :
    ((p : reesAlgebra I) : R[X]).coeff m = 0 := by
  rw [(mem_piece I n p.val).mp p.property, coeff_monomial, ite_eq_right hnm]

lemma components_of_piece (n : ℕ) (p : piece I n) :
    components I p.val = DirectSum.of (fun n => piece I n) n p := by
  ext m : 1
  by_cases h : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    apply Subtype.ext
    apply Subtype.ext
    simp [component_val, piece_coeff_ne I h p]

lemma recompose_components (p : reesAlgebra I) :
    DirectSum.coeAddMonoidHom (piece I) (components I p) = p := by
  let f := DirectSum.coeAddMonoidHom (piece I)
  have hc (n : ℕ) :
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp f)) =
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp
          ((piece I n).subtype.toAddMonoidHom.comp (DFinsupp.evalAddMonoidHom n)))) := by
    apply DirectSum.addHom_ext
    intro m a
    dsimp only [f]
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    change ((a : reesAlgebra I) : R[X]).coeff n =
      (((DirectSum.of (fun i => piece I i) m a) n : reesAlgebra I) : R[X]).coeff n
    by_cases h : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), piece_coeff_ne I h a]
      rfl
  apply Subtype.ext
  ext n
  have h := DFunLike.congr_fun (hc n) (components I p)
  change ((f (components I p) : reesAlgebra I) : R[X]).coeff n =
    ((component I n p : reesAlgebra I) : R[X]).coeff n at h
  simpa only [component_val, coeff_monomial, ite_true, if_true] using h

instance gradedMonoid : SetLike.GradedMonoid (piece I) where
  one_mem := by simp [mem_piece]
  mul_mem {i j} {a b} ha hb := by
    change (a : R[X]) * b = monomial (i+j) (((a : R[X]) * b).coeff (i+j))
    rw [(mem_piece I i a).mp ha, (mem_piece I j b).mp hb,
      monomial_mul_monomial, coeff_monomial, ite_eq_left rfl]

instance grading : GradedAlgebra (piece I) where
  toGradedMonoid := gradedMonoid I
  decompose' := components I
  left_inv := recompose_components I
  right_inv := by
    have h : (componentsAdd I).comp (DirectSum.coeAddMonoidHom (piece I)) = .id _ := by
      apply DirectSum.addHom_ext
      intro n a
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact components_of_piece I n a
    exact DFunLike.congr_fun h

def affineBlowup : Scheme.{u} := Proj (piece I)

def zeroEquiv : R ≃+* piece I 0 :=
  RingEquiv.ofBijective (algebraMap R (piece I 0)) (by
    constructor
    · intro a b h
      have hp := congrArg (fun p : piece I 0 => ((p : reesAlgebra I) : R[X])) h
      exact Polynomial.C_injective hp
    · intro p
      refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (show ((p : reesAlgebra I) : R[X]) =
        C (((p : reesAlgebra I) : R[X]).coeff 0) by
          simpa only [monomial_zero_left] using (mem_piece I 0 p.val).mp p.property).symm)

def zeroIso : CommRingCat.of R ≅ CommRingCat.of (piece I 0) :=
  (zeroEquiv I).toCommRingCatIso

def projection : affineBlowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def generator (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.val, reesAlgebra.monomial_mem.mpr (by simp [a.property])⟩

@[simp] lemma generator_val (a : I) :
    (generator I a : R[X]) = monomial 1 a.val := rfl

lemma generator_mem (a : I) : generator I a ∈ piece I 1 := by
  simp [mem_piece]

def evaluation : reesAlgebra I →+* R :=
  (Polynomial.evalRingHom 1).comp (reesAlgebra I).val.toRingHom

@[simp] lemma evaluation_generator (a : I) : evaluation I (generator I a) = a.val := by
  simp [evaluation]

lemma evaluation_piece {n : ℕ} (p : piece I n) :
    evaluation I p.val = ((p : reesAlgebra I) : R[X]).coeff n := by
  change Polynomial.eval 1 ((p : reesAlgebra I) : R[X]) = _
  conv_lhs => rw [(mem_piece I n p.val).mp p.property]
  simp

abbrev chart (a : I) := HomogeneousLocalization.Away (piece I) (generator I a)

def chartMap (a : I) : chart I a →+* Localization.Away a.val :=
  (IsLocalization.map (M := Submonoid.powers (generator I a))
    (S := Localization.Away (generator I a)) (T := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)).comp
      (algebraMap (chart I a) (Localization.Away (generator I a)))

lemma chartMap_mk (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartMap I a (HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        (evaluation I p) ⟨a.val ^ n, ⟨n, rfl⟩⟩ := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp

lemma chartMap_injective (a : I) : Function.Injective (chartMap I a) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro x hx
  change x = 0
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  have hzero := RingHom.mem_ker.mp hx
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbp⟩ := (IsLocalization.mk'_eq_zero_iff (M := Submonoid.powers a.val)
    (S := Localization.Away a.val) _ _).mp hzero
  obtain ⟨j, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨generator I a ^ j, ⟨j, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hpn : p ∈ piece I n := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff n := evaluation_piece I ⟨p, hpn⟩
  change (generator I a : R[X]) ^ j * (p : R[X]) = 0
  rw [(mem_piece I n p).mp hpn, generator_val, monomial_pow, monomial_mul_monomial]
  rw [he] at hbp
  simp [hbp]

def chartBase (a : I) : R →+* chart I a :=
  (HomogeneousLocalization.fromZeroRingHom (piece I) (Submonoid.powers (generator I a))).comp
    (zeroEquiv I).toRingHom

lemma chartMap_base (a : I) (r : R) :
    chartMap I a (chartBase I a r) = algebraMap R (Localization.Away a.val) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • (1 : ℕ)) := by
    simp [mem_piece]
  refine (chartMap_mk I a 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he]
  convert IsLocalization.mk'_one (M := Submonoid.powers a.val)
    (Localization.Away a.val) r using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Subtype.ext
  exact pow_zero a.val

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ReesCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.ReesGrading

noncomputable section
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma base_pow_mul_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartBase I a (a.val ^ n) *
        HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp =
      chartBase I a (evaluation I p) := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_base, chartMap_mk]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I p) ⟨a.val ^ n, n, rfl⟩

end

noncomputable section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma generators_adjoin : Algebra.adjoin R (Set.range (generator I)) = ⊤ := by
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin]
  have hs : (reesAlgebra I).val '' Set.range (generator I) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    ext p
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨generator I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [hs, adjoin_monomial_eq_reesAlgebra]
  rw [Algebra.map_top, Subalgebra.range_val]

lemma generators_adjoin_zero :
    Algebra.adjoin (piece I 0) (Set.range (generator I)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  have hh : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range (generator I))).algebraMap_mem (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

lemma iSup_generator_basicOpen :
    ⨆ a : I, Proj.basicOpen (piece I) (generator I a) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (generator I)
    (fun a => ⟨1, generator_mem I a⟩) (generators_adjoin_zero I)

def chartCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (chart I a)
  f a := Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)
  map_prop a := inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)))
  idx x := (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (m := 1) (piece I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose_spec

lemma chartCover_projection (a : I) :
    (chartCover I).f a ≫ projection I = Spec.map (CommRingCat.ofHom (chartBase I a)) := by
  change Proj.awayι (m := 1) (piece I) (generator I a) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_ExceptionalIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.BlowupLift
noncomputable section
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsLeftRegular r)

def coefficient (a : I) : S :=
  Classical.choose ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))

lemma mul_coefficient (a : I) : r * coefficient I f r hI a = f a.val := by
  exact (Classical.choose_spec ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))).symm

include hr in

lemma coefficients_span : Ideal.span (Set.range (coefficient I f r hI)) = ⊤ := by
  let K : Ideal S := Ideal.span (Set.range (coefficient I f r hI))
  have hmap : I.map f ≤ Submodule.map (LinearMap.mulLeft S r) K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Submodule.map (LinearMap.mulLeft S r) K
    exact ⟨coefficient I f r hI ⟨a, ha⟩,
      Ideal.subset_span (Set.mem_range_self _), mul_coefficient I f r hI ⟨a, ha⟩⟩
  have hmem : r ∈ Submodule.map (LinearMap.mulLeft S r) K := by
    apply hmap
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨s, hs, hrs⟩ := hmem
  have hs1 : s = 1 := hr (by simpa using hrs)
  refine Ideal.eq_top_of_isUnit_mem (I := K) ?_ isUnit_one
  exact hs1 ▸ hs

end
end MaximalSeshadri.BlowupLift


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PrincipalCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalToLocalization : reesAlgebra I →+* Localization.Away r :=
  (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)).comp (reesAlgebra I).val.toRingHom

lemma principalToLocalization_base (s : R) :
    principalToLocalization I f r (algebraMap R (reesAlgebra I) s) =
      algebraMap S (Localization.Away r) (f s) := by
  simp [principalToLocalization]

lemma principalToLocalization_generator (a : I) :
    principalToLocalization I f r (generator I a) =
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by
  change (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)) (monomial 1 a.val) = _
  simp only [coe_eval₂RingHom, eval₂_monomial, RingHom.comp_apply, pow_one]
  rw [← BlowupLift.mul_coefficient I f r hI a, map_mul]
  calc _ = (algebraMap S (Localization.Away r) r * IsLocalization.Away.invSelf r) *
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by ring
       _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

include hI in
lemma principalToLocalization_range (p : reesAlgebra I) :
    ∃ s : S, algebraMap S (Localization.Away r) s = principalToLocalization I f r p := by
  have hp : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨BlowupLift.coefficient I f r hI a, (principalToLocalization_generator I f r hI a).symm⟩
  | algebraMap s => exact ⟨f s, (principalToLocalization_base I f r s).symm⟩
  | add p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s+t, by rw [map_add, hs, ht, map_add]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s*t, by rw [map_mul, hs, ht, map_mul]⟩

include hr in
lemma principalLocalization_injective : Function.Injective (algebraMap S (Localization.Away r)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))

def principalMap : reesAlgebra I →+* S where
  toFun p := Classical.choose (principalToLocalization_range I f r hI p)
  map_zero' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 0), map_zero, map_zero])
  map_one' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 1), map_one, map_one])
  map_add' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p+q)), map_add,
      map_add, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])
  map_mul' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p*q)), map_mul,
      map_mul, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])

lemma principalMap_spec (p : reesAlgebra I) :
    algebraMap S (Localization.Away r) (principalMap I f r hI hr p) =
      principalToLocalization I f r p :=
  Classical.choose_spec (principalToLocalization_range I f r hI p)

lemma principalMap_base (s : R) :
    principalMap I f r hI hr (algebraMap R (reesAlgebra I) s) = f s := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_base]

lemma principalMap_generator (a : I) :
    principalMap I f r hI hr (generator I a) = BlowupLift.coefficient I f r hI a := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_generator]

lemma principalMap_irrelevant :
    (HomogeneousIdeal.irrelevant (piece I)).toIdeal.map (principalMap I f r hI hr) = ⊤ := by
  rw [eq_top_iff, ← BlowupLift.coefficients_span I f r hI hr.left]
  apply Ideal.span_le.mpr
  rintro s ⟨a, rfl⟩
  rw [← principalMap_generator I f r hI hr]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem (piece I) (by decide : 0 < (1 : ℕ))
    (generator_mem I a)

end

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (X : Scheme.{u}) (f : R →+* Γ(X, ⊤)) (r : Γ(X, ⊤))
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalScheme : X ⟶ affineBlowup I :=
  Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
    (principalMap_irrelevant I f r hI hr)

@[reassoc]
lemma principalScheme_projection :
    principalScheme I X f r hI hr ≫ projection I =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  change Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
      (principalMap_irrelevant I f r hI hr) ≫
      (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext s
  exact principalMap_base I f r hI hr s

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma base_generator_comm (a b : I) :
    algebraMap R (reesAlgebra I) a.val * generator I b =
      algebraMap R (reesAlgebra I) b.val * generator I a := by
  apply Subtype.ext
  change C a.val * monomial 1 b.val = C b.val * monomial 1 a.val
  simp only [C_mul_monomial, mul_comm a.val b.val]

lemma chartHom_ext {S : Type*} [CommRing S] (a : I)
    (g h : chart I a →+* S) (he : g.comp (chartBase I a) = h.comp (chartBase I a))
    (hr : IsRegular (g (chartBase I a a.val))) : g = h := by
  have hb (s : R) : g (chartBase I a s) = h (chartBase I a s) := RingHom.congr_fun he s
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hr.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg h (base_pow_mul_mk I a n p hp)
  simpa only [map_mul, map_pow, hb] using h₁.trans ((hb ((evaluation I) p)).trans h₂.symm)

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.SpecMaps
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

def coordinate (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

lemma coordinate_ext {f g : X ⟶ Spec R} (h : coordinate f = coordinate g) : f = g :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.injective
    (Opposite.unop_injective h)

@[simp] lemma coordinate_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    coordinate (f ≫ g) = coordinate g ≫ f.appTop := by
  simp [coordinate]

@[simp] lemma coordinate_spec (f : R ⟶ S) : coordinate (Spec.map f) = f ≫ (Scheme.ΓSpecIso S).inv := by
  simp [coordinate]

@[simp] lemma coordinate_comp_spec (f : X ⟶ Spec S) (g : R ⟶ S) :
    coordinate (f ≫ Spec.map g) = g ≫ coordinate f := by
  simp [coordinate]

end
end MaximalSeshadri.SpecMaps

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma chart_scheme_ext {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ Spec (CommRingCat.of (chart I a)))
    (he : g ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) =
      h ≫ Spec.map (CommRingCat.ofHom (chartBase I a)))
    (hr : IsRegular (coordinate g (chartBase I a a.val))) : g = h := by
  apply coordinate_ext
  apply CommRingCat.hom_ext
  apply chartHom_ext I a _ _ _ hr
  have hc := congrArg coordinate he
  simp only [coordinate_comp_spec] at hc
  exact congrArg CommRingCat.Hom.hom hc

end
end MaximalSeshadri.ReesGrading


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_Restriction
attribute [-instance] _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.ModulePresheaf
open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}

def pushforwardCongr {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦
    PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsCongr (by subst h; rfl)).app _)
      (fun _ _ _ ↦ by subst h; rfl)) (fun _ ↦ by subst h; rfl)

@[simp] lemma pushforwardCongr_hom_app {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ)
    (M : PresheafOfModules.{v} S) (U) (x) :
    ((pushforwardCongr h).hom.app M).app U x = x := by
  subst h
  rfl

def pushforwardNatTrans (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M := {
    app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app
    (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

variable {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ T)
  (H₁ : whiskerRight (NatTrans.op adj.counit) S = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫
    whiskerRight (NatTrans.op adj.unit) T = 𝟙 T)

def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit := (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
    (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit := (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
    (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (F.map (adj.unit.app U.unop)).op
      (M.map (adj.counit.app (F.obj U.unop)).op x) = x
    change M.obj (Opposite.op (F.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.left_triangle_components, op_id, M.map_id]
    rfl
  right_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (adj.unit.app (G.obj U.unop)).op
      (M.map (G.map (adj.counit.app U.unop)).op x) = x
    change M.obj (Opposite.op (G.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.right_triangle_components, op_id, M.map_id]
    rfl

end MaximalSeshadri.ModulePresheaf

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

def modulePresheafRestrict : PresheafOfModules Y.ringCatSheaf.obj ⥤
    PresheafOfModules X.ringCatSheaf.obj :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

def modulePresheafRestrictAdjunction : modulePresheafRestrict f ⊣
    PresheafOfModules.pushforward f.toRingCatSheafHom.hom := by
  refine ModulePresheaf.pushforwardPushforwardAdj
    (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x
    exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have h : (f.appIso U.unop).inv ≫ f.app _ ≫
        X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]
      rfl
    exact congr($h x)

def moduleSheafificationRestrict :
    PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj) ⋙
      Scheme.Modules.restrictFunctor f ≅
    modulePresheafRestrict f ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (Scheme.Modules.restrictAdjunction f))
    ((modulePresheafRestrictAdjunction f).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)))

end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MonoidalCategory
variable {X : Scheme}

def modulePresheafRestrictOpensIso (U : X.Opens) :
    modulePresheafRestrict U.ι ≅
      PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf := by
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app V := (U.ι.appIso V.unop).inv }
  have h : Functor.whiskerRight α (forget₂ CommRingCat RingCat) = 𝟙 _ := by
    ext V x
    simp only [Functor.whiskerRight_app, α, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  exact ModulePresheaf.pushforwardCongr (F := U.ι.opensFunctor)
    (T := U.toScheme.ringCatSheaf.obj) (S := X.ringCatSheaf.obj) h

def modulePresheafTensorRestrict (U : X.Opens)
    (M N : PresheafOfModules X.ringCatSheaf.obj) :
    (modulePresheafRestrict U.ι).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N) ≅
      PresheafOfModules.Monoidal.tensorObj (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).obj M)
        ((modulePresheafRestrict U.ι).obj N) := by
  letI : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.presheaf)
  exact (modulePresheafRestrictOpensIso U).app _ ≪≫
    (Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf) M N).symm ≪≫
    tensorIso ((modulePresheafRestrictOpensIso U).symm.app M)
      ((modulePresheafRestrictOpensIso U).symm.app N)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorRestrict (U : X.Opens) (M N : X.Modules) :
    (moduleTensor X M N).restrict U.ι ≅
      moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) :=
  (moduleSheafificationRestrict U.ι).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (modulePresheafTensorRestrict U M.val N.val)

def moduleTensorIso {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    moduleTensor X M P ≅ moduleTensor X N Q := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def moduleTensorUnit (M : X.Modules) :
    moduleTensor X (structureSheaf X) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def modulePowFrame {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
    moduleTensorIso e (modulePowFrame U e n) ≪≫ moduleTensorUnit _

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorMap {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    moduleTensor X M P ⟶ moduleTensor X N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f.val g.val)

@[simp] lemma moduleTensorMap_id (M N : X.Modules) :
    moduleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (moduleTensor X M N) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

@[reassoc] lemma moduleTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : Q ⟶ R) (k : R ⟶ T) :
    moduleTensorMap (f ≫ g) (h ≫ k) = moduleTensorMap f h ≫ moduleTensorMap g k := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ g.val) ⊗ₘ (h.val ≫ k.val)) = _
  rw [← tensorHom_comp_tensorHom]
  exact Functor.map_comp _ _ _

def modulePowMap {M N : X.Modules} (f : M ⟶ N) :
    ∀ n, modulePow X M n ⟶ modulePow X N n
  | 0 => 𝟙 _
  | n + 1 => moduleTensorMap f (modulePowMap f n)

@[simp] lemma modulePowMap_id (M : X.Modules) (n : ℕ) :
    modulePowMap (𝟙 M) n = 𝟙 (modulePow X M n) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change moduleTensorMap (𝟙 M) (modulePowMap (𝟙 M) n) = 𝟙 (moduleTensor X M (modulePow X M n))
    rw [hn, moduleTensorMap_id]

@[reassoc] lemma modulePowMap_comp {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    modulePowMap (f ≫ g) n = modulePowMap f n ≫ modulePowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n hn =>
    change moduleTensorMap (f ≫ g) (modulePowMap (f ≫ g) n) =
      moduleTensorMap f (modulePowMap f n) ≫ moduleTensorMap g (modulePowMap g n)
    rw [hn, moduleTensorMap_comp]

def unitPowerIso : ∀ n, modulePow X (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => moduleTensorUnit _ ≪≫ unitPowerIso n

def powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    structureSheaf X ⟶ modulePow X M n :=
  (unitPowerIso n).inv ≫ modulePowMap s n

@[simp] lemma powerSection_zero {M : X.Modules} (s : structureSheaf X ⟶ M) :
    powerSection s 0 = 𝟙 (structureSheaf X) := by
  change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X)
  exact Category.id_comp _

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PowerExtension
attribute [-instance] _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

lemma affine_frame (J : LineBundle Y) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
  exact ⟨⟨U, hU⟩, hyU, ⟨frameOfLE J.sheaf hUV e⟩⟩

end
end MaximalSeshadri.InvertibleLocal


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_LocalEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.UnitEndomorphism
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

def equation (U : X.Opens) : Γ(X, U) := g.val.app (op U) (1 : Γ(X, U))

lemma app_eq_mul (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) a = equation g U * a := by
  let sectionMap : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (g.val.app (op U)).hom
  change sectionMap a = sectionMap 1 * a
  simpa only [smul_eq_mul, mul_one, mul_comm a, one_mul] using sectionMap.map_smul a 1

lemma image_principal (U : X.Opens) :
    (show Ideal Γ(X, U) from (g.val.app (op U)).hom.range) = Ideal.span {equation g U} := by
  ext a
  change (∃ b : Γ(X, U), g.val.app (op U) b = a) ↔ _
  constructor
  · rintro ⟨b, hb⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, hb.symm.trans (app_eq_mul g U b)⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨b, (app_eq_mul g U b).trans hb.symm⟩

lemma equation_regular [Mono g] (U : X.Opens) : IsRegular (equation g U) := by
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
  have hinj := PresheafOfModules.injective_of_mono g.val (op U)
  apply (Commute.isRegular_iff (fun a => Commute.all _ a)).mpr
  intro a b hab
  apply hinj
  exact (app_eq_mul g U a).trans (hab.trans (app_eq_mul g U b).symm)

end
end MaximalSeshadri.UnitEndomorphism
namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

lemma image_eq_comap [IsAffine X] (h : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    sectionImageIdeal J ι U.1 = (I.comap f).ideal U := by
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := by simp [V]
  exact (h.2 U V e).trans (IdealPullback.comap_ideal I f U V e).symm

variable {I f}

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  have : Mono (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) := by
    apply (Scheme.Modules.toPresheafOfModules Z).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    let : Mono ι.val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map ι))
    exact PresheafOfModules.injective_of_mono ι.val (op (j ''ᵁ U.unop))
  let unitIso : (Scheme.Modules.restrictFunctor j).obj (structureSheaf Y) ≅
      structureSheaf Z := Scheme.Modules.restrictUnitIso j
  exact mono_comp (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) unitIso.hom

lemma restricted_image [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  apply Ideal.ext
  intro (r : Γ(Z, U.1))
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔
    (j.appIso U.1).inv r ∈ (I.comap f).ideal
      ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩
  refine Iff.trans ?_ (SetLike.ext_iff.mp (image_eq_comap I f J ι h
    ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩) _)
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) => k (ι.val.app (op (j ''ᵁ U.1)) s))
      (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : CategoryTheory.Iso (C := Z.Modules) (J.sheaf.restrict j) (structureSheaf Z)) :
    ∃ r : Γ(Z, ⊤), IsRegular r ∧
      ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top Z⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit Z ⟶ UnitEndomorphism.unit Z :=
    e.inv ≫ restrictedInclusion J ι j
  have : Mono g := mono_comp (C := Z.Modules) e.inv (restrictedInclusion J ι j)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s)
        e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

lemma affine_local_equation [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
        Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨U, hyU, ⟨e⟩⟩ := affine_frame J y
  refine ⟨U, hyU, ?_⟩
  exact local_equation J ι h U.1.ι e

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

def restrictLineBundle (J : LineBundle Y) (j : Z ⟶ Y) [IsOpenImmersion j] : LineBundle Z where
  sheaf := J.sheaf.restrict j
  locallyRankOne z := by
    obtain ⟨U, hzU, ⟨e⟩⟩ := J.locallyRankOne (j z)
    let V := j ⁻¹ᵁ U
    refine ⟨V, hzU, ⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (j ∣_ U) U.ι).app J.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (j ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (j ∣_ U)
    have e'' : J.sheaf.restrict (V.ι ≫ j) ≅ structureSheaf V.toScheme := by
      simp only [morphismRestrict_ι] at e'
      exact e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι j).app J.sheaf).symm ≪≫ e''

lemma presents_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image J ι hf j U, ← Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal I (j ≫ f) U V e

lemma invertible_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j, presents_restrict I f J ι h j⟩

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma specIdeal_coordinate {Y : Scheme} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) :
    ((specIdeal I).comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      I.map (SpecMaps.coordinate f).hom := by
  rw [comap_top, specIdeal_top, Ideal.map_map]
  rfl

end
end MaximalSeshadri.IdealPullback

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_LocalUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

lemma restricted_image_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) (V : X.affineOpens)
    (hUV : j ''ᵁ U.1 ≤ f ⁻¹ᵁ V.1) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  have he := (h.2 ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ V hUV).trans
    (IdealPullback.comap_ideal I f _ V hUV).symm
  apply Ideal.ext
  intro (r : Γ(Z, U.1))
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔
    (j.appIso U.1).inv r ∈ (I.comap f).ideal
      ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩
  refine Iff.trans ?_ (SetLike.ext_iff.mp he _)
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) =>
      k (ι.val.app (op (j ''ᵁ U.1)) s)) (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : CategoryTheory.Iso (C := U.1.toScheme.Modules)
      (J.sheaf.restrict U.1.ι) (structureSheaf U.1.toScheme)) :
    ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  have : Mono g := mono_comp (C := U.1.toScheme.Modules) e.inv
    (restrictedInclusion J ι U.1.ι)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤,
    ← restricted_image_on_chart J ι h U.1.ι ⟨⊤, isAffineOpen_top _⟩ V
      (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
  ext r
  change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
        k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

lemma local_equations (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨W, hyW, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hyW, hyV⟩)
  refine ⟨⟨U, hU⟩, hyU, ?_⟩
  exact local_equation_on_chart J ι h ⟨U, hU⟩ ⟨V, hV⟩
    (hUV.trans inf_le_right) (frameOfLE J.sheaf (hUV.trans inf_le_left) e)

lemma invertible_iff_local_equations :
    InvertiblePullbackIdeal I f ↔
    ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} :=
  ⟨local_equations, invertible_of_local_equations⟩

lemma invertible_congr {X' : Scheme} {I' : X'.IdealSheafData} {f' : Y ⟶ X'}
    (he : I.comap f = I'.comap f') :
    InvertiblePullbackIdeal I f ↔ InvertiblePullbackIdeal I' f' := by
  rw [invertible_iff_local_equations, invertible_iff_local_equations, he]

end

end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

lemma IsBlowup.postIso (hπ : IsBlowup I π) (e : X ≅ Z)
    (J : Z.IdealSheafData) (he : J.comap e.hom = I) :
    IsBlowup J (π ≫ e.hom) := by
  have hcongr (W : Scheme) (f : W ⟶ X) :
      InvertiblePullbackIdeal J (f ≫ e.hom) ↔ InvertiblePullbackIdeal I f :=
    InvertibleLocal.invertible_congr (by rw [Scheme.IdealSheafData.comap_comp, he])
  refine ⟨(hcongr B π).mpr hπ.1, ?_⟩
  intro W f hf
  have hf' : InvertiblePullbackIdeal I (f ≫ e.inv) := by
    apply (hcongr W (f ≫ e.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ e.inv) hf'
  refine ⟨l, ?_, ?_⟩
  · change l ≫ π ≫ e.hom = f
    rw [← Category.assoc, hl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply huniq m
    rw [← cancel_mono e.hom, Category.assoc, hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

end MaximalSeshadri.Geometry

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

abbrev scheme : Scheme := ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

end
end MaximalSeshadri.AffineBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_PlaneCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading
variable (K : Type) [Field K]
abbrev PlaneRing := MvPolynomial (Fin 2) K

end

end MaximalSeshadri.PlaneBlowup


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.ReesGrading
noncomputable section
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance polynomial_isReduced [_root_.IsReduced R] : _root_.IsReduced R[X] where
  eq_zero p hp := by
    ext n
    exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero

end
end MaximalSeshadri.ReesGrading

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_ActualInterpolation
attribute [-instance] _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MaximalSeshadri.ActualInterpolation
noncomputable section
open scoped Topology
open Filter
open MaximalSeshadri.AnalyticCoordinates

lemma absolute_of_derivativeSummable {c : Exponent → ℂ} {R : ℝ}
    (h : DerivativeSummable c R) : AbsolutelyConvergentAt c R := by
  have hh := h 0 0
  change Summable (fun e : Exponent => ‖c e‖ *
    ((e.1.descFactorial 0 : ℝ) * R^(e.1-0)) *
    ((e.2.descFactorial 0 : ℝ) * R^(e.2-0))) at hh
  simpa [AbsolutelyConvergentAt, mul_assoc, pow_add] using hh

def seriesValueMap (V : Submodule ℂ (Exponent → ℂ)) (R : ℝ)
    (hs : ∀ c ∈ V, DerivativeSummable c R) (p : ℂ × ℂ)
    (hx : ‖p.1‖ ≤ R) (hz : ‖p.2‖ ≤ R) : V →ₗ[ℂ] ℂ where
  toFun c := seriesEval c p.1 p.2
  map_add' c d := seriesEval_add (absolute_of_derivativeSummable (hs c c.property))
    (absolute_of_derivativeSummable (hs d d.property)) hx hz
  map_smul' a c := by
    change (∑' e : Exponent, (a * (c : Exponent → ℂ) e) * p.1^e.1 * p.2^e.2) =
      a * ∑' e : Exponent, (c : Exponent → ℂ) e * p.1^e.1 * p.2^e.2
    simp only [mul_assoc]
    exact tsum_mul_left

variable {A M : Type*} [CommRing A] [Algebra ℂ A]
  [AddCommGroup M] [Module ℂ M]

def germCoefficients (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) : M →ₗ[ℂ] (Exponent → ℂ) :=
  analyticCoefficientLinear.comp ((analyticPullback q hq).toLinearMap.comp coord)

end
end MaximalSeshadri.ActualInterpolation

end



end OAI
end


