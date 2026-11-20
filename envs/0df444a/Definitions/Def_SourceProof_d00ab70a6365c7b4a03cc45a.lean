-- Prove2me | Definitions.Def_SourceProof_d00ab70a6365c7b4a03cc45a
-- name    : SourceProof_d00ab70a6365c7b4a03cc45a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:02:38.931433+00:00
-- url     : https://prove2.me/theorems/c221931f-ed4c-4c5c-99bf-7d6a8b1d4ab1
-- title:
--   LevyStochCalc source module: SourceProof_d00ab70a6365c7b4a03cc45a
-- statement:
--   The original source theorem `LevyStochCalc.Probability.enorm_dyadicRunMax` comes from the `LevyStochCalc.Probability.DoobContinuous` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
  have hcoe : ∀ x : ℝ, 0 ≤ x → ((‖x‖₊ : ℝ≥0) : ℝ) = x := fun x hx => by
    simp [Real.norm_eq_abs, abs_of_nonneg hx]
  refine le_antisymm ?_ ?_
  · rcases Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
      (fun k => ‖M (LevyStochCalc.Probability.dyadicTime T n k) ω‖) with ⟨k, hk, hkeq⟩
    refine le_iSup_of_le ⟨k, Finset.mem_range.mp hk⟩ (le_of_eq ?_)
    rw [LevyStochCalc.Probability.dyadicRunMax, hkeq]
    congr 1
    exact NNReal.eq (by simp [Real.norm_eq_abs])
  · refine iSup_le fun k => ?_
    refine ENNReal.coe_le_coe.mpr ?_
    refine NNReal.coe_le_coe.mp ?_
    rw [hcoe _ (LevyStochCalc.Probability.dyadicRunMax_nonneg M T n ω), coe_nnnorm]
    exact Finset.le_sup' (f := fun j => ‖M (LevyStochCalc.Probability.dyadicTime T n j) ω‖)
      (Finset.mem_range.mpr k.isLt)
/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

end LevyStochCalc.Probability


