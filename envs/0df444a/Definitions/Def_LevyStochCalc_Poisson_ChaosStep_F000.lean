-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F000
-- name    : LevyStochCalc_Poisson_ChaosStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:17:34.768962+00:00
-- url     : https://prove2.me/theorems/0228bfb4-8b0e-4369-81fd-beab55e01356
-- title:
--   Source declarations: LevyStochCalc.Poisson.ChaosStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ChaosStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Definitions.Def_LevyStochCalc_Probability_Charlier_F002

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

/-- The degree-`n` element of the Poisson chaos of the region `B`: the Charlier polynomial of
degree `n` and rate `ν̂(B)`, evaluated at the count `N(B)`. -/
noncomputable def poissonChaosStep (N : PoissonRandomMeasure P ν) (n : ℕ) (B : Set (ℝ × E))
    (ω : Ω) : ℝ :=
  Probability.charlierScaled n (referenceIntensity ν B).toReal (N.N ω B).toReal
@[simp] theorem poissonChaosStep_zero (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 0 B ω = 1 := by
  simp [poissonChaosStep]
/-- The degree-one element of the Poisson chaos of `B` is the compensated count `Ñ(B)`. -/
@[simp] theorem poissonChaosStep_one (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 1 B ω = N.compensated B ω := by
  simp [poissonChaosStep, PoissonRandomMeasure.compensated]
/-- The degree-two element of the Poisson chaos of `B` is `Ñ(B) ^ 2 - N(B)`. -/
theorem poissonChaosStep_two (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 2 B ω = N.compensated B ω ^ 2 - (N.N ω B).toReal := by
  simp [poissonChaosStep, Probability.charlierScaled_two, PoissonRandomMeasure.compensated]
theorem measurable_poissonChaosStep (N : PoissonRandomMeasure P ν) (n : ℕ) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) : Measurable (poissonChaosStep N n B) :=
  (((Probability.continuous_charlierScaled n _).measurable).comp
      ENNReal.measurable_toReal).comp (N.measurable_eval hB)
/-- Transfer of an integral of a function of the count along the Poisson law of that count. -/
private lemma integral_comp_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (N.N ω B).toReal ∂P
      = ∫ k : ℕ, g (k : ℝ) ∂poissonMeasure (referenceIntensity ν B).toNNReal := by
  have hmeas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have hcomp : Measurable (fun x : ℝ≥0∞ => g x.toReal) := hg.comp ENNReal.measurable_toReal
  rw [show (∫ ω, g (N.N ω B).toReal ∂P) = ∫ x, g x.toReal ∂(P.map (fun ω => N.N ω B)) from
    (integral_map hmeas.aemeasurable hcomp.aestronglyMeasurable).symm, N.poisson_law hB hfin]
  change ∫ x, g x.toReal
      ∂((poissonMeasure (referenceIntensity ν B).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞))) = _
  rw [integral_map measurable_from_nat.aemeasurable hcomp.aestronglyMeasurable]
  simp
/-- Transfer of integrability of a function of the count along the Poisson law of that count. -/
theorem integrable_comp_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {g : ℝ → ℝ} (hg : Measurable g)
    (hint : Integrable (fun k : ℕ => g (k : ℝ))
      (poissonMeasure (referenceIntensity ν B).toNNReal)) :
    Integrable (fun ω => g (N.N ω B).toReal) P := by
  have hmeas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have hcomp : Measurable (fun x : ℝ≥0∞ => g x.toReal) := hg.comp ENNReal.measurable_toReal
  rw [show (fun ω => g (N.N ω B).toReal) = (fun x : ℝ≥0∞ => g x.toReal) ∘ (fun ω => N.N ω B) from
    rfl, ← integrable_map_measure hcomp.aestronglyMeasurable hmeas.aemeasurable,
    N.poisson_law hB hfin]
  change Integrable (fun x : ℝ≥0∞ => g x.toReal)
    ((poissonMeasure (referenceIntensity ν B).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞)))
  rw [integrable_map_measure hcomp.aestronglyMeasurable measurable_from_nat.aemeasurable]
  simpa [Function.comp_def] using hint
/-- A product of two Poisson chaos elements of a region of finite intensity is integrable. -/
theorem integrable_poissonChaosStep_mul (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n m : ℕ) :
    Integrable (fun ω => poissonChaosStep N n B ω * poissonChaosStep N m B ω) P := by
  refine integrable_comp_count N hB hfin
    (g := fun x => Probability.charlierScaled n (referenceIntensity ν B).toReal x
      * Probability.charlierScaled m (referenceIntensity ν B).toReal x)
    ((Probability.continuous_charlierScaled n _).mul
      (Probability.continuous_charlierScaled m _)).measurable ?_
  have := Probability.integrable_eval_poissonMeasure (referenceIntensity ν B).toNNReal
    (Probability.charlierPoly (referenceIntensity ν B).toReal n
      * Probability.charlierPoly (referenceIntensity ν B).toReal m)
  simpa only [Polynomial.eval_mul, Probability.charlierScaled] using this
/-- A Poisson chaos element of a region of finite intensity lies in `L²`. -/
theorem memLp_two_poissonChaosStep (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n : ℕ) :
    MemLp (poissonChaosStep N n B) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_poissonChaosStep N n hB).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using integrable_poissonChaosStep_mul N hB hfin n n
/-! ### Complex scalars -/

end LevyStochCalc.Poisson


