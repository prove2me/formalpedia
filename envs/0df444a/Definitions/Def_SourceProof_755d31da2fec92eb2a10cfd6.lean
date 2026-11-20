-- Prove2me | Definitions.Def_SourceProof_755d31da2fec92eb2a10cfd6
-- name    : SourceProof_755d31da2fec92eb2a10cfd6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T14:57:01.285789+00:00
-- url     : https://prove2.me/theorems/9292e897-6ea7-4ece-b4b4-940483bf4ac8
-- title:
--   LevyStochCalc source module: SourceProof_755d31da2fec92eb2a10cfd6
-- statement:
--   The original source theorem `LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax` comes from the `LevyStochCalc.Probability.DoobContinuous` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001

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

/-! ### The supremum over the window -/


theorem _root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun n => ?_)
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · have ht0 : (t : ℝ) = 0 := le_antisymm (hT0 ▸ t.2.2) t.2.1
      refine le_iSup_of_le 0 ?_
      rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
      refine le_iSup_of_le ⟨0, Nat.succ_pos _⟩ (le_of_eq ?_)
      have hd0 : LevyStochCalc.Probability.dyadicTime T 0 0 = 0 := by
        simp [LevyStochCalc.Probability.dyadicTime, ← hT0]
      rw [hd0, ht0]
    · have hbd : ∀ n : ℕ, (‖M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞)
          ≤ ⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
        intro n
        refine le_iSup_of_le n ?_
        rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
        exact le_iSup_of_le
          ⟨LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n, Nat.lt_succ_of_le (LevyStochCalc.Probability.dyadicIndex_le hTpos t.2.2 n)⟩ le_rfl
      have hMs : Filter.Tendsto
          (fun n => M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω) Filter.atTop
          (nhds (M (t : ℝ) ω)) :=
        (LevyStochCalc.Probability.tendsto_nhdsGE_of_nhdsGT (hcad (t : ℝ))).comp
          (LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex hTpos t.2.1 t.2.2)
      have hconv : Filter.Tendsto
          (fun n => (‖M (LevyStochCalc.Probability.dyadicTime T n (LevyStochCalc.Probability.dyadicIndex T (t : ℝ) n)) ω‖₊ : ℝ≥0∞))
          Filter.atTop (nhds ((‖M (t : ℝ) ω‖₊ : ℝ≥0∞))) :=
        (ENNReal.continuous_coe.tendsto _).comp hMs.nnnorm
      exact le_of_tendsto hconv (Filter.Eventually.of_forall hbd)
  · rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
    exact iSup_le fun k =>
      le_iSup_of_le ⟨LevyStochCalc.Probability.dyadicTime T n (k : ℕ), LevyStochCalc.Probability.dyadicTime_mem_Icc hT n (k : ℕ)⟩ le_rfl
/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

end LevyStochCalc.Probability


