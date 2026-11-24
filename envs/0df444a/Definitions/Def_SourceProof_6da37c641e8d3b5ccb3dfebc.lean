-- Prove2me | Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc
-- name    : SourceProof_6da37c641e8d3b5ccb3dfebc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:45.15165+00:00
-- url     : https://prove2.me/theorems/f9e24f67-51b5-4ad9-bb4d-39b0c546515c
-- title:
--   StochLean source theorem: MeasureTheory.stoppedValueWithTerminal_of_ne_top

import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopped values with an explicitly supplied value at infinity

Mathlib's finite-time stopped value is retained whenever the stopping time is
finite. At infinity the supplied terminal variable is used instead of the
totalized `untopA` evaluation. Truncated stopped values converge to this owner
when the process has the stated full-half-line terminal limit.
-/

@[expose] public section

open Filter ProbabilityTheory
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E} {Z : Ω → E} {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc {ω : Ω} (hτ : τ ω ≠ ⊤) :
    stoppedValueWithTerminal X Z τ ω = stoppedValue X τ ω := by
  simp only [MeasureTheory.stoppedValueWithTerminal, if_neg hτ]
end MeasureTheory

namespace ProbabilityTheory.Indistinguishable

open MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → E} {Z W : Ω → E}

end ProbabilityTheory.Indistinguishable


