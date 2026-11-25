-- Prove2me | Definitions.Def_SourceProof_40787295ae568a8b7553a55a
-- name    : SourceProof_40787295ae568a8b7553a55a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:04.424076+00:00
-- url     : https://prove2.me/theorems/b81f3292-1217-4d03-b8d7-676c3bd5c562
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.upperApprox_le_horizon

import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001

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

theorem _root_.Prove2MeSourceProof.h_40787295ae568a8b7553a55a (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    τ.upperApprox T n ω ≤ T := min_le_right _ _
end FiniteStoppingTime

end ProbabilityTheory


