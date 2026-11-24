-- Prove2me | Definitions.Def_SourceProof_13d74fe230d87debed607218
-- name    : SourceProof_13d74fe230d87debed607218
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:22.426797+00:00
-- url     : https://prove2.me/theorems/544c8495-28e8-4cf2-a6ae-641693843294
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.symm

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

protected theorem _root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 (h : Indistinguishable X Y P) : Indistinguishable Y X P := by
  filter_upwards [h] with ω hω t
  exact (hω t).symm
end Indistinguishable

end ProbabilityTheory


