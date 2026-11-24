-- Prove2me | Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000
-- name    : StochLean_Probability_Process_LocalMartingale_InitialValue_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:18.093864+00:00
-- url     : https://prove2.me/theorems/b49cc9fd-50fc-44c0-8ff0-46a906a02ffd
-- title:
--   StochLean: Probability.Process.LocalMartingale.InitialValue F000

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Mathlib.Tactic.Positivity

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial-value safeguards for local martingales

Any finite F₀-measurable random variable defines a constant Protter local
martingale, even without integrability. Unmasked localization cannot remove
the initial value or make an unbounded initial value bounded.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {Z : Ω → ℝ}

/-- A concrete fundamental sequence for a constant process with arbitrary finite initial value. -/
noncomputable def initialValueLocalizer (Z : Ω → ℝ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if |Z ω| ≤ n then ⊤ else 0
end ProbabilityTheory


