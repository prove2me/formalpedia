-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000
-- name    : StochLean_Probability_Process_Stopping_BeforeSigma_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:27.177263+00:00
-- url     : https://prove2.me/theorems/11ebb971-a414-4e58-8ec8-9d7d16b76efa
-- title:
--   StochLean: Probability.Process.Stopping.BeforeSigma F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006

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

/-- The sigma-field of information strictly before `τ`, including initial information. -/
@[instance_reducible] protected def measurableSpaceBefore (_hτ : IsStoppingTime F τ) :
    MeasurableSpace Ω :=
  F 0 ⊔ MeasurableSpace.generateFrom
    {B | ∃ (t : ℝ≥0) (A : Set Ω),
      MeasurableSet[F t] A ∧ B = A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}}
end MeasureTheory.IsStoppingTime


