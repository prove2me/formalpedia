-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigmaOrder_F000
-- name    : StochLean_Probability_Process_Stopping_BeforeSigmaOrder_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:47.114965+00:00
-- url     : https://prove2.me/theorems/dae7cf1d-19a9-4be7-b44c-da28885fe1c3
-- title:
--   StochLean: Probability.Process.Stopping.BeforeSigmaOrder F000

import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Strict comparison events in the pre-stopping sigma-field

Protter III.7 uses a countable union over deterministic times strictly between
the two stopping times. Infinite upper times are allowed. Terminal information
is also measurable before `T` after restriction to `{T = ∞}`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {σ τ : Ω → WithTop ℝ≥0}

private theorem exists_rat_between_withTop {a b : WithTop ℝ≥0} (hab : a < b) :
    ∃ q : ℚ, a < (Real.toNNReal q : WithTop ℝ≥0) ∧
      (Real.toNNReal q : WithTop ℝ≥0) < b := by
  cases a with
  | top => exact False.elim (not_lt_of_ge le_top hab)
  | coe a =>
    cases b with
    | top =>
      obtain ⟨q, _, haq, _⟩ := (NNReal.lt_iff_exists_rat_btwn a (a + 1)).mp
        (lt_add_one a)
      exact ⟨q, WithTop.coe_lt_coe.mpr haq, WithTop.coe_lt_top _⟩
    | coe b =>
      obtain ⟨q, _, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).mp
        (WithTop.coe_lt_coe.mp hab)
      exact ⟨q, WithTop.coe_lt_coe.mpr haq, WithTop.coe_lt_coe.mpr hqb⟩
end MeasureTheory.IsStoppingTime


