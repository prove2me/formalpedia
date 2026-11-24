-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
-- name    : StochLean_Probability_Process_Stopping_TerminalValue_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:05.259901+00:00
-- url     : https://prove2.me/theorems/a09f48c8-9f52-434c-a401-b1a70871af3a
-- title:
--   StochLean: Probability.Process.Stopping.TerminalValue F000

import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

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

/-- Finite stopping uses the existing owner; infinite stopping uses the
explicit terminal variable, never a totalized finite-time value. -/
noncomputable def stoppedValueWithTerminal (X : ℝ≥0 → Ω → E) (Z : Ω → E)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) : E := by
  classical
  exact if τ ω = ⊤ then Z ω else stoppedValue X τ ω
end MeasureTheory

namespace ProbabilityTheory.Indistinguishable

open MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → E} {Z W : Ω → E}

end ProbabilityTheory.Indistinguishable


