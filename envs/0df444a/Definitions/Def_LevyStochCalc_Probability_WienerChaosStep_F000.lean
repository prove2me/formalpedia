-- Prove2me | Definitions.Def_LevyStochCalc_Probability_WienerChaosStep_F000
-- name    : LevyStochCalc_Probability_WienerChaosStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:49:25.913598+00:00
-- url     : https://prove2.me/theorems/5d030dbe-acba-4eab-9521-8efbc62165a8
-- title:
--   Source declarations: LevyStochCalc.Probability.WienerChaosStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.WienerChaosStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000
import Definitions.Def_SourceProof_431e64ab8e52f44314251e91

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Wiener chaos elements of a single step

For a step of variance `v` carrying the increment `x`, the degree-`n` element of the Wiener chaos
of that step is the Hermite polynomial `H_n(x; v)` of variance `v`; at low degrees it is `1`, `x`
and `x ^ 2 - v`. For an increment with law `gaussianReal 0 v` these elements are square integrable
and orthogonal across degrees, with `E[H_n H_m] = δ_(n m) n! v ^ n`, and every element of positive
degree is centred.

## Main statements

* `LevyStochCalc.Probability.wienerChaosStep` — the degree-`n` element, `H_n(x; v)`.
* `LevyStochCalc.Probability.memLp_two_wienerChaosStep` — square integrability.
* `LevyStochCalc.Probability.integral_wienerChaosStep_mul` — `E[H_n H_m] = δ_(n m) n! v ^ n`.
* `LevyStochCalc.Probability.integral_wienerChaosStep_sq` — `E[H_n ^ 2] = n! v ^ n`.
* `LevyStochCalc.Probability.integral_wienerChaosStep` — `E[H_n] = 0` for `n ≠ 0`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-- The degree-`n` element of the Wiener chaos of a step of variance `v` carrying the increment
`x`, the Hermite polynomial `H_n(x; v)`. -/
noncomputable def wienerChaosStep (n : ℕ) (v : ℝ≥0) (x : ℝ) : ℝ := hermiteScaled n (v : ℝ) x
@[simp] theorem wienerChaosStep_zero (v : ℝ≥0) (x : ℝ) : wienerChaosStep 0 v x = 1 := by
  simp [wienerChaosStep]
@[simp] theorem wienerChaosStep_one (v : ℝ≥0) (x : ℝ) : wienerChaosStep 1 v x = x := by
  simp [wienerChaosStep]
/-- The degree-two element of the Wiener chaos of a step, `H_2(x; v) = x ^ 2 - v`. -/
theorem wienerChaosStep_two (v : ℝ≥0) (x : ℝ) : wienerChaosStep 2 v x = x ^ 2 - (v : ℝ) := by
  simp [wienerChaosStep, hermiteScaled_two]
theorem measurable_wienerChaosStep (n : ℕ) (v : ℝ≥0) : Measurable (wienerChaosStep n v) :=
  (hermitePoly (v : ℝ) n).continuous.measurable
/-- A product of two chaos elements of a step is integrable for the law `gaussianReal 0 v`. -/
theorem integrable_wienerChaosStep_mul_gaussianReal (v : ℝ≥0) (n m : ℕ) :
    Integrable (fun x => wienerChaosStep n v x * wienerChaosStep m v x) (gaussianReal 0 v) := by
  have h := integrable_eval_gaussianReal v (hermitePoly (v : ℝ) n * hermitePoly (v : ℝ) m)
  simpa only [eval_mul, wienerChaosStep, hermiteScaled] using h
/-- A chaos element of a step lies in `L²` for the law `gaussianReal 0 v`. -/
theorem memLp_two_wienerChaosStep_gaussianReal (v : ℝ≥0) (n : ℕ) :
    MemLp (wienerChaosStep n v) 2 (gaussianReal 0 v) := by
  refine (memLp_two_iff_integrable_sq
    (measurable_wienerChaosStep n v).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using integrable_wienerChaosStep_mul_gaussianReal v n n
/-- The `L²` pairing of the chaos elements of a step under the law `gaussianReal 0 v`,
`E[H_n H_m] = δ_(n m) n! v ^ n`. -/
theorem integral_wienerChaosStep_mul_gaussianReal (v : ℝ≥0) (n m : ℕ) :
    ∫ x, wienerChaosStep n v x * wienerChaosStep m v x ∂gaussianReal 0 v
      = if n = m then (n.factorial : ℝ) * (v : ℝ) ^ n else 0 := by
  simpa only [wienerChaosStep, hermiteScaled] using _root_.Prove2MeSourceProof.h_431e64ab8e52f44314251e91 v n m
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A chaos element of a step lies in `L²` at an increment with law `gaussianReal 0 v`. -/
theorem memLp_two_wienerChaosStep {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (n : ℕ) : MemLp (fun ω => wienerChaosStep n v (X ω)) 2 P := by
  have h : MemLp (wienerChaosStep n v) 2 (P.map X) := by
    rw [hX.map_eq]; exact memLp_two_wienerChaosStep_gaussianReal v n
  simpa only [Function.comp_def] using h.comp_of_map hX.aemeasurable
/-- A product of two chaos elements of a step is integrable at an increment with law
`gaussianReal 0 v`. -/
theorem integrable_wienerChaosStep_mul {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (n m : ℕ) :
    Integrable (fun ω => wienerChaosStep n v (X ω) * wienerChaosStep m v (X ω)) P := by
  have h : Integrable (fun x => wienerChaosStep n v x * wienerChaosStep m v x) (P.map X) := by
    rw [hX.map_eq]; exact integrable_wienerChaosStep_mul_gaussianReal v n m
  simpa only [Function.comp_def] using h.comp_aemeasurable hX.aemeasurable
/-- The `L²` pairing of the chaos elements of a step at an increment with law `gaussianReal 0 v`,
`E[H_n H_m] = δ_(n m) n! v ^ n`. -/
theorem integral_wienerChaosStep_mul {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (n m : ℕ) :
    ∫ ω, wienerChaosStep n v (X ω) * wienerChaosStep m v (X ω) ∂P
      = if n = m then (n.factorial : ℝ) * (v : ℝ) ^ n else 0 := by
  have hf : AEStronglyMeasurable
      (fun x : ℝ => wienerChaosStep n v x * wienerChaosStep m v x) (gaussianReal 0 v) :=
    ((measurable_wienerChaosStep n v).mul (measurable_wienerChaosStep m v)).aestronglyMeasurable
  have hcomp := hX.integral_comp (f := fun x : ℝ => wienerChaosStep n v x * wienerChaosStep m v x)
    hf
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_wienerChaosStep_mul_gaussianReal]
/-- The chaos elements of a step are centred in positive degree. -/
theorem integral_wienerChaosStep {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {n : ℕ} (hn : n ≠ 0) : ∫ ω, wienerChaosStep n v (X ω) ∂P = 0 := by
  have h := integral_wienerChaosStep_mul hX n 0
  simpa [hn] using h
/-- The `L²` norm of the degree-`n` chaos element of a step, `E[H_n ^ 2] = n! v ^ n`. -/
theorem integral_wienerChaosStep_sq {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (n : ℕ) :
    ∫ ω, wienerChaosStep n v (X ω) ^ 2 ∂P = (n.factorial : ℝ) * (v : ℝ) ^ n := by
  have h := integral_wienerChaosStep_mul hX n n
  simpa [pow_two] using h
end LevyStochCalc.Probability


