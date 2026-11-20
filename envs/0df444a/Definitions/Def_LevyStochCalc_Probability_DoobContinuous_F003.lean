-- Prove2me | Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
-- name    : LevyStochCalc_Probability_DoobContinuous_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:04:15.29005+00:00
-- url     : https://prove2.me/theorems/78071838-2775-4749-a2b0-fbbe4dfd941f
-- title:
--   Source declarations: LevyStochCalc.Probability.DoobContinuous
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.DoobContinuous. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F000
import Definitions.Def_SourceProof_d00ab70a6365c7b4a03cc45a

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

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/

/-- The sampled running maximum of a finite sum is bounded by the sum of the running maxima. -/
theorem enorm_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) := by
  rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
  refine iSup_le fun k => ?_
  have hpt : (‖∑ j ∈ s, A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_le_coe.mpr (nnnorm_sum_le _ _)
  refine le_trans hpt (Finset.sum_le_sum fun j _ => ?_)
  rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
  exact le_iSup (fun m : Fin (2 ^ n + 1) =>
    (‖A j (dyadicTime T n (m : ℕ)) ω‖₊ : ℝ≥0∞)) k
/-- The supremum of the sampled running maxima of a finite sum is bounded by the sum of the
suprema. -/
theorem iSup_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ ∑ j ∈ s, ⨆ n, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_sum_le s A T n ω)
    (Finset.sum_le_sum fun j _ => le_iSup (fun m => (‖dyadicRunMax (A j) T m ω‖₊ : ℝ≥0∞)) n)
end LevyStochCalc.Probability


