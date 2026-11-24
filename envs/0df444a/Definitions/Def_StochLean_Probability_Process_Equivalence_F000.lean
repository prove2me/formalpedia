-- Prove2me | Definitions.Def_StochLean_Probability_Process_Equivalence_F000
-- name    : StochLean_Probability_Process_Equivalence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:44.581098+00:00
-- url     : https://prove2.me/theorems/750edc31-8209-4e04-a384-08e00c79d2e9
-- title:
--   StochLean: Probability.Process.Equivalence F000

import Mathlib.Probability.Process.FiniteDimensionalLaws

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

/-- `X` and `Y` are modifications (versions) of one another when their coordinates agree almost
surely at every fixed time. The exceptional null set may depend on the time. -/
def IsModification (X Y : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ t, X t =ᵐ[P] Y t
/-- Two processes are indistinguishable when their complete trajectories agree on one common
almost-sure event. This is strictly stronger than modification for uncountable time sets. -/
def Indistinguishable (X Y : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω
namespace IsModification

variable {X Y Z : T → Ω → E} {P : Measure Ω}

variable [MeasurableSpace E]

end IsModification

namespace Indistinguishable

variable {X Y Z : T → Ω → E} {P : Measure Ω}

end Indistinguishable

end ProbabilityTheory


