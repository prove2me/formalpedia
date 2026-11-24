-- Prove2me | Definitions.Def_SourceProof_3f8c9bee8c801981db97d019
-- name    : SourceProof_3f8c9bee8c801981db97d019
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:51.190709+00:00
-- url     : https://prove2.me/theorems/7841bb74-1f4f-479c-8530-5a0283d74027
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSpaceBefore_le_ambient

import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Definitions.Def_SourceProof_51740884f3e4929ebdd46661

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

theorem _root_.Prove2MeSourceProof.h_3f8c9bee8c801981db97d019 (hτ : IsStoppingTime F τ) :
    hτ.measurableSpaceBefore ≤ mΩ :=
  (_root_.Prove2MeSourceProof.h_51740884f3e4929ebdd46661 hτ).trans hτ.measurableSpace_le
end MeasureTheory.IsStoppingTime


