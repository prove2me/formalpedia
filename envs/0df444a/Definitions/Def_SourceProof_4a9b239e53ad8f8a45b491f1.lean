-- Prove2me | Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
-- name    : SourceProof_4a9b239e53ad8f8a45b491f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:18.107533+00:00
-- url     : https://prove2.me/theorems/0069781e-b102-4e26-9b14-9607a6013d31
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.ae_eq

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


theorem _root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 (h : Indistinguishable X Y P) (t : T) : X t =ᵐ[P] Y t :=
  h.mono fun _ hω ↦ hω t
end Indistinguishable

end ProbabilityTheory


