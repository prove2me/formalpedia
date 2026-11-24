-- Prove2me | Definitions.Def_SourceProof_6a0407047627b0386a56ee04
-- name    : SourceProof_6a0407047627b0386a56ee04
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:18.049873+00:00
-- url     : https://prove2.me/theorems/49acea20-aa4e-461c-8e97-d1e16a484a12
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.le_measurableSpaceBefore

import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The sigma-field strictly before a stopping time

Protter III.2 defines `F_{T-}` using `F_0` and the events `A ∩ {t < T}`,
where `A ∈ F_t` and `t > 0`. We allow `t = 0` in the sole owner below and
prove that this gives exactly the same sigma-field. This is a subfield of
Mathlib's existing stopped sigma-field, not a replacement for it.

At infinite lifetime this field is `⨆ t, F t`, not necessarily `F_0` or
the ambient sigma-field. No process value at infinity is defined here.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_6a0407047627b0386a56ee04 (hτ : IsStoppingTime F τ) :
    F 0 ≤ hτ.measurableSpaceBefore := le_sup_left
end MeasureTheory.IsStoppingTime


