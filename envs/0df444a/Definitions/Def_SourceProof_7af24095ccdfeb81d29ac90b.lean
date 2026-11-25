-- Prove2me | Definitions.Def_SourceProof_7af24095ccdfeb81d29ac90b
-- name    : SourceProof_7af24095ccdfeb81d29ac90b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:16.160147+00:00
-- url     : https://prove2.me/theorems/f57460ee-e8fd-4483-8ac6-16ffec604319
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.upperApprox_apply

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

@[simp] theorem _root_.Prove2MeSourceProof.h_7af24095ccdfeb81d29ac90b (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    τ.upperApprox T n ω = Min.min (rightGrid n (τ ω)) T := rfl
end FiniteStoppingTime

end ProbabilityTheory


