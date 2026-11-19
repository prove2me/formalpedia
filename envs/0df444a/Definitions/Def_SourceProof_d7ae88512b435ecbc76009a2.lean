-- Prove2me | Definitions.Def_SourceProof_d7ae88512b435ecbc76009a2
-- name    : SourceProof_d7ae88512b435ecbc76009a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:00:17.810599+00:00
-- url     : https://prove2.me/theorems/e505f3b4-4e96-4b2a-8a1c-4b2884fbd08d
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm
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


theorem _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F G : ℕ → α → ℂ} {F' G' : α → ℂ} (hF : ∀ n, MemLp (F n) 2 m) (hG : ∀ n, MemLp (G n) 2 m)
    (hF' : MemLp F' 2 m) (hG' : MemLp G' 2 m)
    (hFc : Tendsto (fun n => eLpNorm (fun x => F n x - F' x) 2 m) atTop (𝓝 0))
    (hGc : Tendsto (fun n => eLpNorm (fun x => G n x - G' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂m) atTop (𝓝 (∫ x, F' x * G' x ∂m)) := by
  have hconj : ∀ {H : α → ℂ}, MemLp H 2 m → MemLp (fun x => starRingEnd ℂ (H x)) 2 m :=
    fun hH => hH.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hH.1)
      (Eventually.of_forall fun x => (Complex.norm_conj _).symm)
  have key : ∀ (H K : α → ℂ) (hH : MemLp H 2 m) (hK : MemLp K 2 m),
      ∫ x, H x * K x ∂m = inner ℂ ((hconj hH).toLp _) (hK.toLp K) := by
    intro H K hH hK
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hconj hH).coeFn_toLp, hK.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hFc' : Tendsto (fun n => eLpNorm ((fun x => starRingEnd ℂ (F n x))
      - fun x => starRingEnd ℂ (F' x)) 2 m) atTop (𝓝 0) := by
    refine hFc.congr fun n => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [Pi.sub_apply, ← map_sub, Complex.norm_conj]
  have hu := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hconj (hF n)) _ (hconj hF')).2
    hFc'
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG G' hG').2 hGc
  rw [key F' G' hF' hG']
  exact (hu.inner hv).congr fun n => (key _ _ (hF n) (hG n)).symm
end LevyStochCalc.Probability


