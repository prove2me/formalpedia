-- Prove2me | Definitions.Def_SourceProof_0859bfd91b5c292257b9a768
-- name    : SourceProof_0859bfd91b5c292257b9a768
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:52:09.712625+00:00
-- url     : https://prove2.me/theorems/a93281c5-7fb2-4ac9-b7b6-53878828e110
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyOptional.stronglyMeasurable_stoppedValueWithTerminal

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_96b55b0bbab7c4daf4fac947
import Definitions.Def_SourceProof_af738b42523733338f272770

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Optional stopping and measurable values

Optional processes need not themselves be cadlag. Stopping preserves optionality
by transporting each generator, using cadlag paths only for those generators.
Possibly infinite sampling uses the existing explicitly supplied terminal owner.
-/

@[expose] public section

open ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

namespace IsStronglyOptional
theorem _root_.Prove2MeSourceProof.h_0859bfd91b5c292257b9a768
    {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} (hX : IsStronglyOptional F X)
    (hZ : StronglyMeasurable[⨆ t, F t] Z) (hτ : IsStoppingTime F τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValueWithTerminal X Z τ) :=
  (_root_.Prove2MeSourceProof.h_af738b42523733338f272770 (_root_.Prove2MeSourceProof.h_96b55b0bbab7c4daf4fac947 hX)) hZ hτ
end IsStronglyOptional

end MeasureTheory


