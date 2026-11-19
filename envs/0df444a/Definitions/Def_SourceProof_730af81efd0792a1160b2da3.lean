-- Prove2me | Definitions.Def_SourceProof_730af81efd0792a1160b2da3
-- name    : SourceProof_730af81efd0792a1160b2da3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:17:25.68921+00:00
-- url     : https://prove2.me/theorems/000d158f-6e96-434c-b2ac-791cd09ad4c2
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.eventually_jumpSum_leftPt
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums


theorem _root_.Prove2MeSourceProof.h_730af81efd0792a1160b2da3 (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, jumpSum S c (leftPt t n s) = jumpSumStrict S c s := by
  obtain ⟨δ, hδ, hgap⟩ := LevyStochCalc.Analysis.exists_gap S s
  have hlim : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul t
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  refine LevyStochCalc.Analysis.jumpSum_eq_jumpSumStrict S c (LevyStochCalc.Analysis.leftPt_lt ht n hs) fun p hp ⟨h1, h2⟩ => ?_
  have := hgap p hp h2
  have := LevyStochCalc.Analysis.le_leftPt_add ht n hs
  linarith
end Sums

section Dirac

variable [MeasurableSpace E] [MeasurableSingletonClass E]

end Dirac

end LevyStochCalc.Analysis


