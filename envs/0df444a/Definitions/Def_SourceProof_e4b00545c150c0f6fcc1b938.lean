-- Prove2me | Definitions.Def_SourceProof_e4b00545c150c0f6fcc1b938
-- name    : SourceProof_e4b00545c150c0f6fcc1b938
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:23:53.824649+00:00
-- url     : https://prove2.me/theorems/47ec214c-eafc-50ce-b1b9-e4269f205c26
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_stoppedProcess

import Definitions.Def_SourceProof_3167c9529a23dc145fa8582c
import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_6e9bb4c834a1b44d569cca8b
import Definitions.Def_SourceProof_8510e2a398f823aff8350c3b
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_9627c7bfbc6b93307efa4944
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_d0b901b94fc3806e9c302bc2
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.12: stopping the constructed Chapter II integral

Stopping the integral, stopping its integrator, and cutting off the integrand
on the closed stochastic interval give indistinguishable processes. The proof
passes the actual source identities through UCP convergence and uniqueness.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_e4b00545c150c0f6fcc1b938
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_3167c9529a23dc145fa8582c hX) hF hτ).stochasticIntegral hF ha hr)
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  apply (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b ((_root_.Prove2MeSourceProof.h_3167c9529a23dc145fa8582c hX) hF hτ))
    hF ha hr hS huS
  · have heq : (fun n ↦ (hS n).elementaryIntegralProcess (MeasureTheory.stoppedProcess X τ)) =
        fun n ↦ MeasureTheory.stoppedProcess ((hS n).elementaryIntegralProcess X) τ := by
      funext n
      exact (_root_.Prove2MeSourceProof.h_d0b901b94fc3806e9c302bc2 (hS n)) X τ
    rw [heq]
    exact (_root_.Prove2MeSourceProof.h_6e9bb4c834a1b44d569cca8b ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS)) τ
  · exact (_root_.Prove2MeSourceProof.h_9127ba9e47e57c570411dae8 (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr))) τ
end IsSemimartingale

end ProbabilityTheory


