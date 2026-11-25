-- Prove2me | Definitions.Def_SourceProof_af738b42523733338f272770
-- name    : SourceProof_af738b42523733338f272770
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:34.245721+00:00
-- url     : https://prove2.me/theorems/28d38623-24d6-4f78-af93-bd25d311379b
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyProgressive.stronglyMeasurable_stoppedValueWithTerminal

import Definitions.Def_StochLean_Probability_Process_Filtration_Terminal_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_6229da19f14c641cf213eeef
import Definitions.Def_SourceProof_c10dd1089c46a135f8a3af74

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Native stopping measurability of terminal-valued evaluation

A terminal-filtration-measurable input becomes measurable at the stopping
time after restriction to its infinite-time event. Ambient measurability alone
is not substituted for this terminal condition.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {Y : Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

namespace IsStronglyProgressive
theorem _root_.Prove2MeSourceProof.h_af738b42523733338f272770
    (hX : IsStronglyProgressive F X) (hY : StronglyMeasurable[⨆ t, F t] Y)
    (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValueWithTerminal X Y τ) := by
  classical
  have hA : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
    (measurableSet_singleton _).preimage hτ.measurable
  have h := ((_root_.Prove2MeSourceProof.h_c10dd1089c46a135f8a3af74 hY) hτ).add
    ((measurable_stoppedValue hX hτ).stronglyMeasurable.indicator hA.compl)
  have he : MeasureTheory.stoppedValueWithTerminal X Y τ =
      {ω | τ ω = ⊤}.indicator Y + {ω | τ ω = ⊤}ᶜ.indicator (stoppedValue X τ) := by
    funext ω
    by_cases ht : τ ω = ⊤ <;> simp [MeasureTheory.stoppedValueWithTerminal, Set.indicator, ht]
  rwa [he]
end IsStronglyProgressive

end MeasureTheory


