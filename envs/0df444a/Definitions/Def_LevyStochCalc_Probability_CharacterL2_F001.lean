-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
-- name    : LevyStochCalc_Probability_CharacterL2_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:39:17.366258+00:00
-- url     : https://prove2.me/theorems/3dba0362-a2c0-4ef3-b567-da432bb585a8
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

/-- Real functions converging in `L²` converge in `L²` as complex functions. -/
theorem tendsto_eLpNorm_ofReal_sub {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (Y n x : ℂ) - (Y' x : ℂ)) 2 m) atTop (𝓝 0) :=
  hc.congr fun n => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
    rw [← Complex.ofReal_sub, Complex.norm_real])
end LevyStochCalc.Probability


