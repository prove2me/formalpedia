-- Prove2me | Definitions.Def_LevyStochCalc_Probability_WienerChaosExpansion_F000
-- name    : LevyStochCalc_Probability_WienerChaosExpansion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:49:51.836178+00:00
-- url     : https://prove2.me/theorems/ca31f1a2-bf32-49f0-8fa7-84db513af14f
-- title:
--   Source declarations: LevyStochCalc.Probability.WienerChaosExpansion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.WienerChaosExpansion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F001
import Definitions.Def_LevyStochCalc_Probability_L2Series_F001
import Definitions.Def_LevyStochCalc_Probability_WienerChaosStep_F000
import Definitions.Def_SourceProof_b750ef8bbdd7c269127a06e5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponential vector of a Wiener step and its chaos expansion

For a step of variance `v` carrying the increment `x`, the exponential vector at the frequency
`a` is `V(x) = e^(i a x + a ^ 2 v / 2)`, and the degree-`r` chaos element of the step scaled by
`(i a) ^ r / r!` is `C_r(x) = ((i a) ^ r / r!) H_r(x; v)`. The Hermite generating function at the
purely imaginary scalar `t = i a` says that `∑_r C_r(x) = V(x)` for every `x`.

For an increment `X` with law `gaussianReal 0 v` the chaos elements are square integrable with
`E‖C_r(X)‖ ^ 2 = (a ^ 2 v) ^ r / r!`, so their `L²` norms are summable; the modulus of `V(X)` is
the constant `e^(a ^ 2 v / 2)`, so `V(X)` is square integrable as well. The series therefore
converges in `L²(P)` to `V(X)`: absolute summability of the `L²` norms gives a limit in `L²`, and
that limit is identified with the everywhere pointwise sum through convergence in measure. The
second moments add up to the second moment of the modulus of the exponential vector,
`E‖V(X)‖ ^ 2 = e^(a ^ 2 v)`.

The frequency `a` is a free real parameter: nothing here identifies `V` with a random variable
of any model, nor the elements `C_r` with components of an increment of any process.

## Main definitions

* `LevyStochCalc.Probability.wienerExpVector` — the exponential vector `e^(i a x + a ^ 2 v / 2)`.
* `LevyStochCalc.Probability.wienerChaosStepC` — the scaled chaos element
  `((i a) ^ r / r!) H_r(x; v)`.

## Main statements

* `LevyStochCalc.Probability.norm_wienerExpVector` — the modulus is `e^(a ^ 2 v / 2)`.
* `LevyStochCalc.Probability.hasSum_wienerChaosStepC` — `∑_r C_r(x) = V(x)` pointwise.
* `LevyStochCalc.Probability.integral_norm_sq_wienerChaosStepC` —
  `E‖C_r(X)‖ ^ 2 = (a ^ 2 v) ^ r / r!`.
* `LevyStochCalc.Probability.hasSum_toLp_wienerChaosStepC` — the series converges in `L²(P)`
  to the exponential vector.
* `LevyStochCalc.Probability.tendsto_eLpNorm_sum_wienerChaosStepC` — the same as convergence of
  the `L²` norms of the partial-sum errors to `0`.
* `LevyStochCalc.Probability.integral_norm_sq_wienerExpVector` — `E‖V(X)‖ ^ 2 = e^(a ^ 2 v)`.
* `LevyStochCalc.Probability.hasSum_integral_norm_sq_wienerChaosStepC` — the second moments of
  the chaos elements sum to `E‖V(X)‖ ^ 2`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exponential vector of a step of variance `v` at frequency `a` carrying the increment
`x`: `e ^ (i a x + a ^ 2 v / 2)`. -/
noncomputable def wienerExpVector (v : ℝ≥0) (a x : ℝ) : ℂ :=
  Complex.exp (Complex.I * a * x + a ^ 2 * (v : ℝ) / 2)
/-- The modulus of the exponential vector of a step is `e ^ (a ^ 2 v / 2)`. -/
theorem norm_wienerExpVector (v : ℝ≥0) (a x : ℝ) :
    ‖wienerExpVector v a x‖ = Real.exp (a ^ 2 * (v : ℝ) / 2) := by
  have h : Complex.I * (a : ℂ) * (x : ℂ) + (a : ℂ) ^ 2 * ((v : ℝ) : ℂ) / 2
      = ((a ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) + ((a * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [wienerExpVector, h, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
/-- The exponential vector of a step is measurable in the increment. -/
theorem measurable_wienerExpVector (v : ℝ≥0) (a : ℝ) : Measurable (wienerExpVector v a) :=
  Complex.measurable_exp.comp (by fun_prop)
/-- The degree-`r` chaos element of a step of variance `v` scaled by `(i a) ^ r / r !`. -/
noncomputable def wienerChaosStepC (r : ℕ) (v : ℝ≥0) (a x : ℝ) : ℂ :=
  (Complex.I * a) ^ r / (r.factorial : ℂ) * (wienerChaosStep r v x : ℂ)
/-- The scaled chaos elements of a step sum pointwise to its exponential vector. -/
theorem hasSum_wienerChaosStepC (v : ℝ≥0) (a x : ℝ) :
    HasSum (fun r : ℕ => wienerChaosStepC r v a x) (wienerExpVector v a x) :=
  hasSum_hermiteScaled_I (v : ℝ) x a
variable {X : Ω → ℝ} {v : ℝ≥0}

/-- A scaled chaos element of a step lies in `L²` at an increment with law
`gaussianReal 0 v`. -/
theorem memLp_two_wienerChaosStepC (hX : HasLaw X (gaussianReal 0 v) P) (a : ℝ) (r : ℕ) :
    MemLp (fun ω => wienerChaosStepC r v a (X ω)) 2 P :=
  ((memLp_two_wienerChaosStep hX r).ofReal).const_mul _
/-- The exponential vector at an increment with law `gaussianReal 0 v` lies in `L²`. -/
theorem memLp_two_wienerExpVector [IsFiniteMeasure P] (hX : HasLaw X (gaussianReal 0 v) P)
    (a : ℝ) : MemLp (fun ω => wienerExpVector v a (X ω)) 2 P :=
  MemLp.of_bound
    (((measurable_wienerExpVector v a).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable)
    (Real.exp (a ^ 2 * (v : ℝ) / 2))
    (Filter.Eventually.of_forall fun ω => le_of_eq (norm_wienerExpVector v a (X ω)))
/-- The second moment of the modulus of a scaled chaos element of a step at an increment with
law `gaussianReal 0 v`, `(a ^ 2 v) ^ r / r !`. -/
theorem integral_norm_sq_wienerChaosStepC (hX : HasLaw X (gaussianReal 0 v) P) (a : ℝ) (r : ℕ) :
    ∫ ω, ‖wienerChaosStepC r v a (X ω)‖ ^ 2 ∂P
      = (a ^ 2 * (v : ℝ)) ^ r / (r.factorial : ℝ) := by
  have hpt : ∀ ω : Ω, ‖wienerChaosStepC r v a (X ω)‖ ^ 2
      = ((a ^ 2) ^ r / ((r.factorial : ℝ) ^ 2)) * wienerChaosStep r v (X ω) ^ 2 := by
    intro ω
    rw [wienerChaosStepC, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, div_pow, ← pow_mul, mul_comm r 2, pow_mul, sq_abs, sq_abs]
  rw [show (fun ω => ‖wienerChaosStepC r v a (X ω)‖ ^ 2)
      = fun ω => ((a ^ 2) ^ r / ((r.factorial : ℝ) ^ 2)) * wienerChaosStep r v (X ω) ^ 2 from
    funext hpt, integral_const_mul, integral_wienerChaosStep_sq hX r]
  have hr : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  field_simp
  ring
/-- The scaled chaos elements of a step sum in `L²(P)` to its exponential vector at an increment
with law `gaussianReal 0 v`. -/
theorem hasSum_toLp_wienerChaosStepC [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (a : ℝ) :
    HasSum (fun r : ℕ => (memLp_two_wienerChaosStepC hX a r).toLp
        (fun ω => wienerChaosStepC r v a (X ω)))
      ((memLp_two_wienerExpVector hX a).toLp (fun ω => wienerExpVector v a (X ω))) := by
  refine hasSum_toLp_of_summable_norm _ _ ?_ (Filter.Eventually.of_forall fun ω =>
    hasSum_wienerChaosStepC v a (X ω))
  refine Summable.congr (_root_.Prove2MeSourceProof.h_b750ef8bbdd7c269127a06e5
    (x := a ^ 2 * (v : ℝ)) (by positivity)) fun r => ?_
  rw [integral_norm_sq_wienerChaosStepC hX a r]
/-- The partial sums of the scaled chaos elements of a step converge in `L²(P)` to its
exponential vector at an increment with law `gaussianReal 0 v`. -/
theorem tendsto_eLpNorm_sum_wienerChaosStepC [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (a : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω => (∑ r ∈ Finset.range n, wienerChaosStepC r v a (X ω))
        - wienerExpVector v a (X ω)) 2 P) atTop (𝓝 0) := by
  have h := (hasSum_toLp_wienerChaosStepC hX a).tendsto_sum_nat
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h
  refine h.congr fun n => eLpNorm_congr_ae ?_
  have hco := coeFn_sum_range
    (fun r : ℕ => (memLp_two_wienerChaosStepC hX a r).toLp
      (fun ω => wienerChaosStepC r v a (X ω))) n
  have hall : ∀ᵐ ω ∂P, ∀ r : ℕ,
      ((memLp_two_wienerChaosStepC hX a r).toLp
        (fun ω => wienerChaosStepC r v a (X ω)) : Ω → ℂ) ω = wienerChaosStepC r v a (X ω) :=
    ae_all_iff.2 fun r => (memLp_two_wienerChaosStepC hX a r).coeFn_toLp
  filter_upwards [hco, hall, (memLp_two_wienerExpVector hX a).coeFn_toLp] with ω h1 h2 h3
  simp only [Pi.sub_apply, h1, h3]
  exact congrArg₂ _ (Finset.sum_congr rfl fun r _ => h2 r) rfl
/-- The second moment of the modulus of the exponential vector of a step of variance `v` at
frequency `a` is `e ^ (a ^ 2 v)`. -/
theorem integral_norm_sq_wienerExpVector [IsProbabilityMeasure P] (a : ℝ) :
    ∫ ω, ‖wienerExpVector v a (X ω)‖ ^ 2 ∂P = Real.exp (a ^ 2 * (v : ℝ)) := by
  have hpt : ∀ ω : Ω, ‖wienerExpVector v a (X ω)‖ ^ 2 = Real.exp (a ^ 2 * (v : ℝ)) := by
    intro ω
    rw [norm_wienerExpVector, ← Real.exp_nat_mul]
    ring_nf
  simp [hpt]
/-- The second moments of the scaled chaos elements of a step at an increment with law
`gaussianReal 0 v` sum to the second moment of the modulus of its exponential vector. -/
theorem hasSum_integral_norm_sq_wienerChaosStepC [IsProbabilityMeasure P]
    (hX : HasLaw X (gaussianReal 0 v) P) (a : ℝ) :
    HasSum (fun r : ℕ => ∫ ω, ‖wienerChaosStepC r v a (X ω)‖ ^ 2 ∂P)
      (∫ ω, ‖wienerExpVector v a (X ω)‖ ^ 2 ∂P) := by
  rw [integral_norm_sq_wienerExpVector (X := X) (v := v) a, Real.exp_eq_exp_ℝ]
  refine HasSum.congr_fun (NormedSpace.expSeries_div_hasSum_exp (a ^ 2 * (v : ℝ))) fun r => ?_
  rw [integral_norm_sq_wienerChaosStepC hX a r]
end LevyStochCalc.Probability


