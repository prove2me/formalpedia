-- Prove2me | Definitions.Def_SourceProof_73c70764ff89ea6093f75bd8
-- name    : SourceProof_73c70764ff89ea6093f75bd8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:21.435956+00:00
-- url     : https://prove2.me/theorems/0b6e3013-69a8-4cfb-918d-4e2b168fc129
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.trans

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Modification and indistinguishability of stochastic processes

The two relations in this file deliberately have different quantifier order. A modification may
use a different null set at every time; indistinguishability requires one common full-measure event
on which the complete trajectories agree.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

namespace IsModification

variable {X Y Z : T → Ω → E} {P : Measure Ω}

variable [MeasurableSpace E]

end IsModification

namespace Indistinguishable

variable {X Y Z : T → Ω → E} {P : Measure Ω}

protected theorem _root_.Prove2MeSourceProof.h_73c70764ff89ea6093f75bd8 (hXY : Indistinguishable X Y P) (hYZ : Indistinguishable Y Z P) :
    Indistinguishable X Z P := by
  filter_upwards [hXY, hYZ] with ω hXYω hYZω t
  exact (hXYω t).trans (hYZω t)
end Indistinguishable

end ProbabilityTheory


