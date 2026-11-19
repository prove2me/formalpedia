-- Prove2me | Definitions.Def_SourceProof_68e898bacd09d59b5244b471
-- name    : SourceProof_68e898bacd09d59b5244b471
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:56:40.373253+00:00
-- url     : https://prove2.me/theorems/be6fe54a-0209-4c03-a272-910f1d22157c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.tendsto_leftPt
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The dyadic partition of an interval

The dyadic partition of `[0, t]` of level `n`, its strict monotonicity, and the left endpoint
`leftPt t n s` of the cell containing a time `s ∈ (0, t]`, which tends to `s` from below.
-/

open Filter
open scoped Topology

namespace LevyStochCalc.Analysis

section Grid


theorem _root_.Prove2MeSourceProof.h_68e898bacd09d59b5244b471 {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => leftPt t n s) atTop (𝓝 s) := by
  have hlo : ∀ n : ℕ, s - t / 2 ^ n ≤ LevyStochCalc.Analysis.leftPt t n s := fun n => by
    linarith [LevyStochCalc.Analysis.le_leftPt_add ht n hs]
  have hhi : ∀ n : ℕ, LevyStochCalc.Analysis.leftPt t n s ≤ s := fun n => (LevyStochCalc.Analysis.leftPt_lt ht n hs).le
  have h1 : Tendsto (fun n : ℕ => s - t / 2 ^ n) atTop (𝓝 s) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul t
    simp only [mul_zero] at this
    have h2 : (fun n : ℕ => s - t / 2 ^ n) = fun n => s - t * (1 / 2) ^ n := by
      funext n; rw [one_div, inv_pow, ← div_eq_mul_inv]
    rw [h2]
    simpa using (tendsto_const_nhds (x := s)).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlo hhi
end Grid

end LevyStochCalc.Analysis


