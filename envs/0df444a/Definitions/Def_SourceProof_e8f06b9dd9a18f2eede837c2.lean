-- Prove2me | Definitions.Def_SourceProof_e8f06b9dd9a18f2eede837c2
-- name    : SourceProof_e8f06b9dd9a18f2eede837c2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:57.427238+00:00
-- url     : https://prove2.me/theorems/63d571de-5d21-41eb-8ccb-6c0efec5028a
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.le_upperApprox

import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001
import Definitions.Def_SourceProof_5a9e4b64f838761a6226e9d1

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

theorem _root_.Prove2MeSourceProof.h_e8f06b9dd9a18f2eede837c2 (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (n : ℕ) (ω : Ω) : τ ω ≤ τ.upperApprox T n ω :=
  le_min (_root_.Prove2MeSourceProof.h_5a9e4b64f838761a6226e9d1 n (τ ω)) (hτ ω)
end FiniteStoppingTime

end ProbabilityTheory


