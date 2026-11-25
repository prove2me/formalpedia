-- Prove2me | Definitions.Def_SourceProof_8c40de8f67b8fcdd3a3ee5e5
-- name    : SourceProof_8c40de8f67b8fcdd3a3ee5e5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:35.076607+00:00
-- url     : https://prove2.me/theorems/35a3980f-7d34-585c-9983-911208ee01dc
-- title:
--   StochLean source theorem: StochLean.continuous_stieltjes_of_nullSingletonClass

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesSubmeasure_F000
import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuous and jump parts of an increasing right-continuous path

Both parts start at zero and use the original Stieltjes measure. Continuity of
the diffuse part follows from the singleton/left-jump formula, including the
bottom endpoint. The original initial value remains a separate term.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8c40de8f67b8fcdd3a3ee5e5 (f : StieltjesFunction ℝ≥0)
    [NullSingletonClass f.measure] : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  have hr : rightLim f t = f t :=
    f.mono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
      ((f.right_continuous t).mono Ioi_subset_Ici_self)
  have hz : ENNReal.ofReal (f t - leftLim f t) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hz
  have hge := f.mono.leftLim_le (le_refl t)
  have hl : leftLim f t = f t := by linarith
  exact hl.trans hr.symm
end StochLean


