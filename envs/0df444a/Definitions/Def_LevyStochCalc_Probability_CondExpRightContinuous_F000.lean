-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CondExpRightContinuous_F000
-- name    : LevyStochCalc_Probability_CondExpRightContinuous_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:40:56.640852+00:00
-- url     : https://prove2.me/theorems/ff51f719-157b-431f-a277-2ddb0bbdc691
-- title:
--   Source declarations: LevyStochCalc.Probability.CondExpRightContinuous
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CondExpRightContinuous. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CondExpInf_F000
import Mathlib.Probability.Process.Filtration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right continuity in `L²` of the conditional expectation along a right-continuous filtration

For a filtration `ℱ` indexed by `ℝ` the σ-algebras `ℱ (t + 1/(n+1))` form an antitone sequence
whose infimum is `⨅ r > t, ℱ r`, which is `ℱ t` when `ℱ` is right-continuous. The `L²`
conditional expectations therefore converge to `𝔼[f | ℱ t]` along that sequence
(`LevyStochCalc.Probability.CondExpInf`), and `r ↦ ‖𝔼[f | ℱ r] − 𝔼[f | ℱ t]‖` is monotone on
`[t, ∞)` because the subspaces `lpMeas (ℱ r)` grow, so the convergence upgrades from the sequence
to the filter `𝓝[>] t`.

## Main statements

* `iInf_filtration_add_one_div` — `⨅ n, ℱ (t + 1/(n+1)) = ⨅ r > t, ℱ r`.
* `tendsto_condExpL2_nhdsGT` — `𝔼[f | ℱ r] → 𝔼[f | ℱ t]` in `L²` as `r ↓ t`.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}

section Sequence

variable (ℱ : Filtration ℝ m₀) (t : ℝ)

/-- The sequence `t + 1/(n+1)` is a strictly decreasing sequence of times above `t`. -/
theorem lt_add_one_div (n : ℕ) : t < t + 1 / (n + 1 : ℝ) := by
  have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  linarith
/-- Evaluating a filtration along `t + 1/(n+1)` gives an antitone sequence of σ-algebras. -/
theorem antitone_filtration_add_one_div :
    Antitone fun n : ℕ => ℱ (t + 1 / (n + 1 : ℝ)) := by
  intro a b hab
  refine ℱ.mono ?_
  have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hab
  have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
    apply one_div_le_one_div_of_le _ hab'
    positivity
  linarith
/-- The σ-algebras of a filtration along `t + 1/(n+1)` have infimum `⨅ r > t, ℱ r`. -/
theorem iInf_filtration_add_one_div :
    ⨅ n : ℕ, ℱ (t + 1 / (n + 1 : ℝ)) = ⨅ r > t, ℱ r := by
  refine le_antisymm (le_iInf₂ fun r hr => ?_) (le_iInf fun n => ?_)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
    exact iInf_le_of_le n (ℱ.mono (by linarith))
  · exact iInf₂_le_of_le (t + 1 / (n + 1 : ℝ)) (lt_add_one_div t n) le_rfl
/-- Along a right-continuous filtration the σ-algebras `ℱ (t + 1/(n+1))` have infimum `ℱ t`. -/
theorem iInf_filtration_add_one_div_of_isRightContinuous [ℱ.IsRightContinuous] :
    ⨅ n : ℕ, ℱ (t + 1 / (n + 1 : ℝ)) = ℱ t := by
  rw [iInf_filtration_add_one_div, ← ℱ.rightCont_eq t, Filtration.IsRightContinuous.eq]
end Sequence

end LevyStochCalc.Probability


