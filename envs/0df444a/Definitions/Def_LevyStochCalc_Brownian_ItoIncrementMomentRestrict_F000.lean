-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
-- name    : LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:07:57.292958+00:00
-- url     : https://prove2.me/theorems/31713110-60c6-4083-ba19-98acf5a33fd7
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIncrementMomentRestrict
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIncrementMomentRestrict. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Restriction of a simple predictable integrand to `(a, b]`

An adapted simple integrand `G` multiplied by the simple integrand `1_{(a, b]}` on their common
refinement is again an adapted simple integrand: its evaluation is `1_{(a, b]}·G`, its
coefficients vanish on every tile not contained in `(a, b]` and stay bounded by any bound on the
coefficients of `G`, and the variance budget of that per-tile bound is at most `C²(b − a)`.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)
/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => if_neg fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact if_pos hs
/-- A simple integrand with coefficients bounded by `C ≥ 0` has evaluations bounded by `C`. -/
theorem SimplePredictable.abs_eval_le {T : ℝ} (H : SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C := by
  classical
  by_cases h : ∃ j : Fin H.N, H.partition j.castSucc < s ∧ s ≤ H.partition j.succ
  · obtain ⟨j, hj⟩ := h
    rw [H.eval_of_mem_Ioc j hj ω]
    exact hC j ω
  · push Not at h
    have hz : H.eval s ω = 0 := by
      unfold SimplePredictable.eval
      exact Finset.sum_eq_zero fun j _ =>
        if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz, abs_zero]
    exact hC0
end LevyStochCalc.Brownian.Ito


