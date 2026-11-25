-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001
-- name    : StochLean_Probability_Process_Stopping_Approximation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:16.260197+00:00
-- url     : https://prove2.me/theorems/e242ad18-7556-4e33-86b7-989c6b33cf48
-- title:
--   StochLean: Probability.Process.Stopping.Approximation F001

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_8d231227f004d115d9169458

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Upper-grid approximations of finite stopping times

These generic helpers were originally used in the Brownian strong Markov
proof. They now live at the stopping-time owner so optional sampling and
localization reuse the same construction. Existing public names are retained.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

/-- Countable-range upper approximation, capped at a deterministic finite horizon. -/
noncomputable def upperApprox (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    FiniteStoppingTime F :=
  (⟨fun ω ↦ rightGrid n (τ ω), _root_.Prove2MeSourceProof.h_8d231227f004d115d9169458 τ.isStoppingTime n⟩ :
    FiniteStoppingTime F).min (const F T)
end FiniteStoppingTime

end ProbabilityTheory


