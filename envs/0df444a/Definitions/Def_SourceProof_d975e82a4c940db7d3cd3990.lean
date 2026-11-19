-- Prove2me | Definitions.Def_SourceProof_d975e82a4c940db7d3cd3990
-- name    : SourceProof_d975e82a4c940db7d3cd3990
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:00:06.096789+00:00
-- url     : https://prove2.me/theorems/03f6fed4-f7a5-463c-b278-7f2622c30610
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
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


theorem _root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m
      ≤ ENNReal.ofReal |u| * eLpNorm (fun x => Y n x - Y' x) 2 m := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
    have h1 : Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))
          * (Complex.exp (Complex.I * ((u * (Y n x - Y' x) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [h1, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Real.norm_eq_abs, ← abs_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))
  have h := ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal |u|)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hbound
end LevyStochCalc.Probability


