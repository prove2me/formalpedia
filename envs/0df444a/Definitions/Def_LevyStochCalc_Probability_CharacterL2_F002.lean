-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002
-- name    : LevyStochCalc_Probability_CharacterL2_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:39:41.479524+00:00
-- url     : https://prove2.me/theorems/0d650fdb-91fd-4404-945b-125e5d48bfc6
-- title:
--   Source declarations: LevyStochCalc.Probability.CharacterL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CharacterL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters of real variables in `L²`

For a real frequency `u` the character `x ↦ e^{iux}` has modulus one and is `|u|`-Lipschitz, and
`e^{iux} − 1` is bounded by `|u| |x|` and by two. So along `L²` convergence of real variables
`Y_n → Y` the characters `e^{iuY_n}` converge in `L²`, and a square-integrable `Y` gives a
square-integrable `e^{iuY} − 1` on any measure and a square-integrable `e^{iuY}` on a finite one.
The complex pairing `∫ F G` is the `L²` inner product of `F̄` and `G`, so it is continuous along
`L²` convergence in each argument.

## Main statements

* `LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two` — `‖e^{it} − 1‖ ≤ 2`.
* `LevyStochCalc.Probability.integrable_exp_I_mul_mul` — a character times an integrable
  variable is integrable.
* `LevyStochCalc.Probability.memLp_exp_I_mul`, `LevyStochCalc.Probability.memLp_exp_I_mul_sub_one`
  — square integrability of `e^{iuY}` and of `e^{iuY} − 1`.
* `LevyStochCalc.Probability.memLp_mul_of_norm_le` — a bounded multiple of a square-integrable
  variable is square integrable.
* `LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm` — continuity of the complex
  pairing along `L²` convergence.
* `LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_mul_sub_mul` — `L²` convergence passes to the complex
  embedding, to the characters and to bounded multiples.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

/-- Multiplication by a bounded complex function preserves `L²` convergence. -/
theorem tendsto_eLpNorm_mul_sub_mul {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Z : α → ℂ} {C : ℝ} (hZC : ∀ x, ‖Z x‖ ≤ C) {X : ℕ → α → ℂ} {X' : α → ℂ}
    (hc : Tendsto (fun n => eLpNorm (fun x => X n x - X' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Z x * X n x - Z x * X' x) 2 m) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun x => Z x * X n x - Z x * X' x) 2 m
      ≤ ENNReal.ofReal C * eLpNorm (fun x => X n x - X' x) 2 m := fun n =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hZC x) (norm_nonneg _)) 2
  have h := ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal C)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hbound
end LevyStochCalc.Probability


