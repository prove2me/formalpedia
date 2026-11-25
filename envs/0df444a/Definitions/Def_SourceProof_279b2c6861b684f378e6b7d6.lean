-- Prove2me | Definitions.Def_SourceProof_279b2c6861b684f378e6b7d6
-- name    : SourceProof_279b2c6861b684f378e6b7d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:50:49.277055+00:00
-- url     : https://prove2.me/theorems/9bee99f2-4952-5b76-a136-bdd3cd4540ea
-- title:
--   StochLean source theorem: MeasureTheory.IsStronglyOptional.stronglyMeasurable_finiteStoppingTime

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_96b55b0bbab7c4daf4fac947

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
theorem _root_.Prove2MeSourceProof.h_279b2c6861b684f378e6b7d6
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyOptional F X) (τ : FiniteStoppingTime F) :
    StronglyMeasurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) :=
  (measurable_stoppedValue (_root_.Prove2MeSourceProof.h_96b55b0bbab7c4daf4fac947 hX) τ.isStoppingTime).stronglyMeasurable
end IsStronglyOptional

end MeasureTheory


