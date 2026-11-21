-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpVector_F000
-- name    : LevyStochCalc_Poisson_ProfileExpVector_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:35:24.373318+00:00
-- url     : https://prove2.me/theorems/c9e6ec2e-a07e-4168-adee-217f22caff49
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpVector
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpVector. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponential vector of a step at a mark profile

For a Poisson random measure with intensity `ν`, a deterministic mark profile `f : E → ℝ`, a
step `(a, b]` and a real frequency `u`, the exponential vector of the step at `f` is the
character of the compensated integral `J(f)` of `f` over the step divided by the Lévy
character of `f` at the step,

  `𝓔_u(f) = exp (i u J(f)) · exp (−(b − a) ∫ ψ_u(f) dν)`,   `ψ_u(x) = e^{iux} − 1 − iux`.

The first factor has modulus one, so at every sample point the modulus of `𝓔_u(f)` is the
deterministic constant `exp (−(b − a) ℜ ∫ ψ_u(f) dν)`. The exponential vector is therefore
bounded and lies in every `Lᵖ(P)`, and its second moment is `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν)`.
The real part of the exponent is `∫ (cos (u f) − 1) dν ≤ 0`, so the modulus is at least one.
For a square-integrable profile the Lévy character of `J(f)` gives `E[𝓔_u(f)] = 1`, and the
variance is `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν) − 1`.

## Main definitions

* `LevyStochCalc.Poisson.profileExpVector` — the exponential vector of a step at a mark profile.

## Main statements

* `LevyStochCalc.Poisson.re_integral_levyCharIntegrand` — the real part of the Lévy
  characteristic exponent is `∫ (cos (u f) − 1) dν`.
* `LevyStochCalc.Poisson.re_integral_levyCharIntegrand_nonpos` — and it is nonpositive.
* `LevyStochCalc.Poisson.integral_profileExpVector` — the exponential vector has mean one.
* `LevyStochCalc.Poisson.norm_profileExpVector` — its modulus is `exp (−(b − a) ℜ ∫ ψ_u(f) dν)`
  at every sample point.
* `LevyStochCalc.Poisson.one_le_norm_profileExpVector` — that modulus is at least one.
* `LevyStochCalc.Poisson.memLp_profileExpVector` — it lies in every `Lᵖ(P)`.
* `LevyStochCalc.Poisson.integral_norm_sq_profileExpVector` — its second moment is
  `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν)`.
* `LevyStochCalc.Poisson.integral_norm_sub_one_sq_profileExpVector` — its variance is
  `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν) − 1`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The real part of the Lévy characteristic exponent -/

/-- The real part of the Lévy characteristic integrand is `cos (u x) − 1`. -/
theorem re_levyCharIntegrand (u x : ℝ) :
    (levyCharIntegrand u x).re = Real.cos (u * x) - 1 := by
  rw [levyCharIntegrand, Complex.sub_re, Complex.sub_re, Complex.one_re, mul_comm Complex.I,
    Complex.exp_ofReal_mul_I_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, sub_zero]
omit [SigmaFinite ν] in
/-- The real part of the Lévy characteristic exponent of a square-integrable mark profile is
`∫ (cos (u f) − 1) dν`. -/
theorem re_integral_levyCharIntegrand (u : ℝ) {f : E → ℝ} (hf : MemLp f 2 ν) :
    (∫ e, levyCharIntegrand u (f e) ∂ν).re = ∫ e, (Real.cos (u * f e) - 1) ∂ν := by
  have h := integral_re (integrable_levyCharIntegrand u hf)
  simp only [RCLike.re_to_complex, re_levyCharIntegrand] at h
  exact h.symm
omit [SigmaFinite ν] in
/-- The real part of the Lévy characteristic exponent of a mark profile is nonpositive. -/
theorem re_integral_levyCharIntegrand_nonpos (u : ℝ) (f : E → ℝ) :
    (∫ e, levyCharIntegrand u (f e) ∂ν).re ≤ 0 := by
  by_cases hi : Integrable (fun e => levyCharIntegrand u (f e)) ν
  · have h := integral_re hi
    simp only [RCLike.re_to_complex, re_levyCharIntegrand] at h
    rw [← h]
    refine integral_nonpos fun e => ?_
    simp only [Pi.zero_apply]
    linarith [Real.cos_le_one (u * f e)]
  · rw [integral_undef hi, Complex.zero_re]
/-! ### The exponential vector -/

/-- The exponential vector of the step `(a, b]` at the mark profile `f` and the frequency `u`:
the character `exp (i u J(f))` of the compensated integral `J(f)` of `f` over the step times
`exp (−(b − a) ∫ ψ_u(f) dν)`, with `ψ_u` the Lévy characteristic integrand. -/
noncomputable def profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b u : ℝ)
    (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * ((u * compensatedProfile N f a b ω : ℝ) : ℂ))
    * Complex.exp (-(((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν))
/-- The exponential vector of a step at a mark profile is measurable. -/
theorem measurable_profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b u : ℝ) :
    Measurable (profileExpVector N f a b u) :=
  (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_const.mul (measurable_compensatedProfile N f a b))))).mul_const _
/-- **The modulus of the exponential vector.** At every sample point the modulus of the
exponential vector of a step at a mark profile is `exp (−(b − a) ℜ ∫ ψ_u(f) dν)`. -/
theorem norm_profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b u : ℝ) (ω : Ω) :
    ‖profileExpVector N f a b u ω‖
      = Real.exp (-((b - a) * (∫ e, levyCharIntegrand u (f e) ∂ν).re)) := by
  rw [profileExpVector, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp,
    Complex.neg_re, Complex.re_ofReal_mul]
/-- The modulus of the exponential vector of a step at a mark profile is at least one. -/
theorem one_le_norm_profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ) {a b : ℝ}
    (hab : a ≤ b) (u : ℝ) (ω : Ω) : 1 ≤ ‖profileExpVector N f a b u ω‖ := by
  rw [norm_profileExpVector, Real.one_le_exp_iff, neg_nonneg]
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hab)
    (re_integral_levyCharIntegrand_nonpos u f)
/-- The exponential vector of a step at a mark profile lies in every `Lᵖ(P)`. -/
theorem memLp_profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b u : ℝ)
    (p : ℝ≥0∞) : MemLp (profileExpVector N f a b u) p P :=
  MemLp.of_bound (measurable_profileExpVector N f a b u).aestronglyMeasurable _
    (Eventually.of_forall fun ω => (norm_profileExpVector N f a b u ω).le)
/-- **The mean of the exponential vector.** The exponential vector of a step at a
square-integrable mark profile has mean one. -/
theorem integral_profileExpVector (N : PoissonRandomMeasure P ν) {f : E → ℝ} (hf : MemLp f 2 ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, profileExpVector N f a b u ω ∂P = 1 := by
  simp only [profileExpVector]
  rw [integral_mul_const, integral_exp_I_mul_compensatedProfile_of_memLp N hf ha hab u,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
/-- **The second moment of the exponential vector.** The exponential vector of a step at a mark
profile has second moment `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν)`. -/
theorem integral_norm_sq_profileExpVector (N : PoissonRandomMeasure P ν) (f : E → ℝ)
    (a b u : ℝ) :
    ∫ ω, ‖profileExpVector N f a b u ω‖ ^ 2 ∂P
      = Real.exp (-(2 * (b - a) * (∫ e, levyCharIntegrand u (f e) ∂ν).re)) := by
  simp_rw [norm_profileExpVector]
  rw [integral_const, probReal_univ, one_smul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
/-- **The variance of the exponential vector.** The exponential vector of a step at a
square-integrable mark profile has variance `exp (−2 (b − a) ℜ ∫ ψ_u(f) dν) − 1`. -/
theorem integral_norm_sub_one_sq_profileExpVector (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, ‖profileExpVector N f a b u ω - 1‖ ^ 2 ∂P
      = Real.exp (-(2 * (b - a) * (∫ e, levyCharIntegrand u (f e) ∂ν).re)) - 1 := by
  have hpt : ∀ z : ℂ, ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hV : Integrable (profileExpVector N f a b u) P :=
    memLp_one_iff_integrable.1 (memLp_profileExpVector N f a b u 1)
  have hsq : Integrable (fun ω => ‖profileExpVector N f a b u ω‖ ^ 2) P := by
    simp_rw [norm_profileExpVector]
    exact integrable_const _
  have hre : ∫ ω, (profileExpVector N f a b u ω).re ∂P = 1 := by
    have h := integral_re hV
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_profileExpVector N hf ha hab u, Complex.one_re]
  have hre2 : Integrable (fun ω => 2 * (profileExpVector N f a b u ω).re) P :=
    hV.re.const_mul 2
  have hdiff : Integrable (fun ω => ‖profileExpVector N f a b u ω‖ ^ 2
      - 2 * (profileExpVector N f a b u ω).re) P := hsq.sub hre2
  simp_rw [hpt]
  rw [integral_add hdiff (integrable_const 1), integral_sub hsq hre2, integral_const_mul,
    integral_const, probReal_univ, one_smul, integral_norm_sq_profileExpVector, hre]
  ring
end LevyStochCalc.Poisson


