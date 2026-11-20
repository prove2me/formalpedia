-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F001
-- name    : LevyStochCalc_Poisson_ChaosStep_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:00:24.258238+00:00
-- url     : https://prove2.me/theorems/851b7cdd-ae8c-4060-8860-2ca9664f375a
-- title:
--   Source declarations: LevyStochCalc.Poisson.ChaosStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ChaosStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F000
import Definitions.Def_SourceProof_730b6b4ed31325bc6f4a68a4

open private integral_comp_count from Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Poisson chaos element of one strip at the mark-constant level

For a Poisson random measure `N` with reference intensity `ν̂ = volume.restrict [0, ∞) ⊗ ν` and a
region `B` of finite intensity, `poissonChaosStep N n B` is the Charlier polynomial of degree `n`
and rate `λ = ν̂(B)` evaluated at the count `N(B)`. On the strip `B = (a, b] ×ˢ A` the rate is
`(b - a) ν(A)`, the degree-one element is the compensated count `Ñ(B)` and the degree-two element
is `Ñ(B) ^ 2 - N(B)`. Under `P` the elements of positive degree are centred and the family is
orthogonal, with `E[C_n C_m] = δ_(n m) n! λ ^ n`; both come from the Charlier orthogonality under
a Poisson law, transferred along the law of the count.

Only a single mark set is covered: these are polynomials of the one count `N(B)`, with no mark
profile beyond the indicator of `A`, so the rate enters only through `ν̂(B)`.

## Main statements

* `LevyStochCalc.Poisson.poissonChaosStep_one` — the degree-one element is `Ñ(B)`.
* `LevyStochCalc.Poisson.poissonChaosStep_two` — the degree-two element is `Ñ(B) ^ 2 - N(B)`.
* `LevyStochCalc.Poisson.integrable_poissonChaosStep_mul` — a product of two elements of a region
  of finite intensity is integrable.
* `LevyStochCalc.Poisson.memLp_two_poissonChaosStep` — an element of a region of finite intensity
  lies in `L²`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_mul` — `E[C_n C_m] = δ_(n m) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_eq_zero` — `E[C_n] = 0` for `n ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_strip_mul` — the same on a strip `(a, b] ×ˢ A`,
  with rate `(b - a) ν(A)`.
* `LevyStochCalc.Poisson.referenceIntensity_strip_ne_top`,
  `LevyStochCalc.Poisson.referenceIntensity_strip_toReal` — the intensity of such a strip is
  finite and equals `(b - a) ν(A)`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_mul` — the same orthogonality at a complex
  scalar: `E[(c^n C_n) (c'^m C_m)] = δ_(n m) c^n c'^n n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_norm_sq_poissonChaosStepC` —
  `E[‖c^n C_n‖ ^ 2] = ‖c‖ ^ (2n) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_sq` —
  `E[(c^n C_n) ^ 2] = c ^ (2n) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStepC_strip_mul` — the complex-scaled bilinear
  moment on a strip `(a, b] ×ˢ A`, with rate `(b - a) ν(A)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The Poisson chaos elements of positive degree of a region of finite intensity are centred
under `P`. -/
theorem integral_poissonChaosStep_eq_zero (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, poissonChaosStep N n B ω ∂P = 0 := by
  have hr : (((referenceIntensity ν B).toNNReal : ℝ≥0) : ℝ) = (referenceIntensity ν B).toReal :=
    ENNReal.coe_toNNReal_eq_toReal _
  rw [show (fun ω => poissonChaosStep N n B ω)
      = fun ω => Probability.charlierScaled n (referenceIntensity ν B).toReal
          (N.N ω B).toReal from rfl]
  rw [integral_comp_count N hB hfin (Probability.continuous_charlierScaled n _).measurable, ← hr]
  exact Probability.integral_charlierPoly_eq_zero (referenceIntensity ν B).toNNReal hn
/-- The `L²` norm of a Poisson chaos element of a region of finite intensity,
`E[C_n ^ 2] = n! λ ^ n` for the rate `λ = ν̂(B)`. -/
theorem integral_poissonChaosStep_sq (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n : ℕ) :
    ∫ ω, poissonChaosStep N n B ω ^ 2 ∂P
      = (n.factorial : ℝ) * (referenceIntensity ν B).toReal ^ n := by
  simpa [pow_two] using _root_.Prove2MeSourceProof.h_730b6b4ed31325bc6f4a68a4 N hB hfin n n
private lemma referenceIntensity_strip {a b : ℝ} (ha : 0 ≤ a) (A : Set E) :
    referenceIntensity ν (Set.Ioc a b ×ˢ A) = ENNReal.ofReal (b - a) * ν A := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Set.Ioc a b ⊆ Set.Ici 0 from fun x hx => ha.trans hx.1.le), Real.volume_Ioc]
/-- The reference intensity of a strip `(a, b] ×ˢ A` over a mark set of finite intensity is
finite. -/
lemma referenceIntensity_strip_ne_top {a b : ℝ} (ha : 0 ≤ a) {A : Set E}
    (hAν : ν A ≠ ⊤) : referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_strip ha]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAν
/-- The reference intensity of a strip `(a, b] ×ˢ A` is `(b - a) ν(A)` as a real number. -/
lemma referenceIntensity_strip_toReal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (A : Set E) :
    (referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal = (b - a) * (ν A).toReal := by
  rw [referenceIntensity_strip ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a)]
/-- The Poisson chaos elements of a strip `(a, b] ×ˢ A` over a mark set of finite intensity are
orthogonal under `P`, with `E[C_n C_m] = δ_(n m) n! λ ^ n` for the rate `λ = (b - a) ν(A)`. -/
theorem integral_poissonChaosStep_strip_mul (N : PoissonRandomMeasure P ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m : ℕ) :
    ∫ ω, poissonChaosStep N n (Set.Ioc a b ×ˢ A) ω
        * poissonChaosStep N m (Set.Ioc a b ×ˢ A) ω ∂P
      = if n = m then (n.factorial : ℝ) * ((b - a) * (ν A).toReal) ^ n else 0 := by
  rw [_root_.Prove2MeSourceProof.h_730b6b4ed31325bc6f4a68a4 N (measurableSet_Ioc.prod hA)
      (referenceIntensity_strip_ne_top ha hAν) n m,
    referenceIntensity_strip_toReal ha hab A]
/-- The Poisson chaos elements of positive degree of a strip `(a, b] ×ˢ A` over a mark set of
finite intensity are centred under `P`. -/
theorem integral_poissonChaosStep_strip_eq_zero (N : PoissonRandomMeasure P ν) {a b : ℝ}
    (ha : 0 ≤ a) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, poissonChaosStep N n (Set.Ioc a b ×ˢ A) ω ∂P = 0 :=
  integral_poissonChaosStep_eq_zero N (measurableSet_Ioc.prod hA)
    (referenceIntensity_strip_ne_top ha hAν) hn
/-! ### Complex scalars -/

/-- The bilinear second moment of two complex-scaled Poisson chaos elements of a region of
finite intensity. -/
theorem integral_poissonChaosStepC_mul (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (c c' : ℂ) (n m : ℕ) :
    ∫ ω, (c ^ n * (poissonChaosStep N n B ω : ℂ)) * (c' ^ m * (poissonChaosStep N m B ω : ℂ)) ∂P
      = if n = m then c ^ n * c' ^ n * (n.factorial : ℂ)
          * ((referenceIntensity ν B).toReal : ℂ) ^ n else 0 := by
  have hpoint : ∀ ω : Ω,
      (c ^ n * (poissonChaosStep N n B ω : ℂ)) * (c' ^ m * (poissonChaosStep N m B ω : ℂ))
        = (c ^ n * c' ^ m) * ((poissonChaosStep N n B ω * poissonChaosStep N m B ω : ℝ) : ℂ) := by
    intro ω; push_cast; ring
  rw [show (fun ω => (c ^ n * (poissonChaosStep N n B ω : ℂ))
        * (c' ^ m * (poissonChaosStep N m B ω : ℂ)))
      = fun ω => (c ^ n * c' ^ m)
        * ((poissonChaosStep N n B ω * poissonChaosStep N m B ω : ℝ) : ℂ) from
    funext hpoint]
  rw [integral_const_mul, integral_complex_ofReal, _root_.Prove2MeSourceProof.h_730b6b4ed31325bc6f4a68a4 N hB hfin n m]
  by_cases h : n = m
  · subst h
    simp only [if_true]
    push_cast
    ring
  · simp [h]
/-- The second moment of the modulus of a complex-scaled Poisson chaos element of a region of
finite intensity. -/
theorem integral_norm_sq_poissonChaosStepC (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (c : ℂ) (n : ℕ) :
    ∫ ω, ‖c ^ n * (poissonChaosStep N n B ω : ℂ)‖ ^ 2 ∂P
      = ‖c‖ ^ (2 * n) * ((n.factorial : ℝ) * (referenceIntensity ν B).toReal ^ n) := by
  have hpoint : ∀ ω : Ω, ‖c ^ n * (poissonChaosStep N n B ω : ℂ)‖ ^ 2
      = ‖c‖ ^ (2 * n) * poissonChaosStep N n B ω ^ 2 := by
    intro ω
    rw [norm_mul, norm_pow, Complex.norm_real, mul_pow, ← pow_mul, Real.norm_eq_abs,
      sq_abs, mul_comm n 2]
  rw [show (fun ω => ‖c ^ n * (poissonChaosStep N n B ω : ℂ)‖ ^ 2)
      = fun ω => ‖c‖ ^ (2 * n) * poissonChaosStep N n B ω ^ 2 from funext hpoint,
    integral_const_mul, integral_poissonChaosStep_sq N hB hfin n]
/-- The bilinear second moment of a complex-scaled Poisson chaos element of a region of finite
intensity. -/
theorem integral_poissonChaosStepC_sq (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (c : ℂ) (n : ℕ) :
    ∫ ω, (c ^ n * (poissonChaosStep N n B ω : ℂ)) ^ 2 ∂P
      = c ^ (2 * n) * (n.factorial : ℂ) * ((referenceIntensity ν B).toReal : ℂ) ^ n := by
  have h := integral_poissonChaosStepC_mul N hB hfin c c n n
  simp only [if_true] at h
  rw [show (fun ω => (c ^ n * (poissonChaosStep N n B ω : ℂ)) ^ 2)
      = fun ω => (c ^ n * (poissonChaosStep N n B ω : ℂ))
        * (c ^ n * (poissonChaosStep N n B ω : ℂ)) from funext fun ω => sq _]
  rw [h, ← pow_add]
  ring_nf
/-- The bilinear second moment of two complex-scaled Poisson chaos elements of a strip
`(a, b] ×ˢ A` over a mark set of finite intensity, with rate `(b - a) ν(A)`. -/
theorem integral_poissonChaosStepC_strip_mul (N : PoissonRandomMeasure P ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (c c' : ℂ) (n m : ℕ) :
    ∫ ω, (c ^ n * (poissonChaosStep N n (Set.Ioc a b ×ˢ A) ω : ℂ))
        * (c' ^ m * (poissonChaosStep N m (Set.Ioc a b ×ˢ A) ω : ℂ)) ∂P
      = if n = m then c ^ n * c' ^ n * (n.factorial : ℂ)
          * (((b - a) * (ν A).toReal : ℝ) : ℂ) ^ n else 0 := by
  rw [integral_poissonChaosStepC_mul N (measurableSet_Ioc.prod hA)
      (referenceIntensity_strip_ne_top ha hAν) c c' n m,
    referenceIntensity_strip_toReal ha hab A]
end LevyStochCalc.Poisson


