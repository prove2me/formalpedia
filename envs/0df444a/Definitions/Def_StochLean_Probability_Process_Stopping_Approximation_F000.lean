-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F000
-- name    : StochLean_Probability_Process_Stopping_Approximation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:10.991858+00:00
-- url     : https://prove2.me/theorems/08a13426-2466-4dfe-8a16-f3586d54ad4f
-- title:
--   StochLean: Probability.Process.Stopping.Approximation F000

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006

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

/-- The source-standard upper dyadic approximation `2⁻ⁿ ⌈2ⁿ t⌉`. -/
noncomputable def dyadicRightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  rightGrid (2 ^ n - 1) t
namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

end FiniteStoppingTime

end ProbabilityTheory


