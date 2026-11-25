-- Prove2me | Definitions.Def_SourceProof_f6e38702caec580acfe72e3b
-- name    : SourceProof_f6e38702caec580acfe72e3b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:57.627884+00:00
-- url     : https://prove2.me/theorems/ba9c88dc-c98b-48bd-a8d1-b16899ffafcb
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.tendsto_upperApprox

import Definitions.Def_SourceProof_2dbf89257579d06e7dcc14c0
import Definitions.Def_SourceProof_7af24095ccdfeb81d29ac90b
import Definitions.Def_SourceProof_e8f06b9dd9a18f2eede837c2

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

theorem _root_.Prove2MeSourceProof.h_f6e38702caec580acfe72e3b (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (ω : Ω) : Tendsto (fun n ↦ τ.upperApprox T n ω) atTop
      (nhdsWithin (τ ω) (Set.Ici (τ ω))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n ↦ (_root_.Prove2MeSourceProof.h_e8f06b9dd9a18f2eede837c2 τ) hτ n ω⟩
  simpa only [_root_.Prove2MeSourceProof.h_7af24095ccdfeb81d29ac90b, min_eq_left (hτ ω)] using
    (_root_.Prove2MeSourceProof.h_2dbf89257579d06e7dcc14c0 (τ ω)).min (tendsto_const_nhds (x := T))
end FiniteStoppingTime

end ProbabilityTheory


