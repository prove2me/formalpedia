-- Prove2me | Definitions.Def_SourceProof_9c038e074e5d5bfe1fc302cb
-- name    : SourceProof_9c038e074e5d5bfe1fc302cb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:26.741809+00:00
-- url     : https://prove2.me/theorems/19896618-a6fb-4533-b53b-46762c026331
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.countable_range_upperApprox

import Definitions.Def_StochLean_Probability_Process_Stopping_Approximation_F001
import Definitions.Def_SourceProof_0f8a0101c88cc3ddfc313b0a

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

theorem _root_.Prove2MeSourceProof.h_9c038e074e5d5bfe1fc302cb (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (Set.range (τ.upperApprox T n)).Countable := by
  apply ((_root_.Prove2MeSourceProof.h_0f8a0101c88cc3ddfc313b0a n).image (fun t ↦ Min.min t T)).mono
  rintro t ⟨ω, rfl⟩
  exact ⟨rightGrid n (τ ω), ⟨τ ω, rfl⟩, rfl⟩
end FiniteStoppingTime

end ProbabilityTheory


