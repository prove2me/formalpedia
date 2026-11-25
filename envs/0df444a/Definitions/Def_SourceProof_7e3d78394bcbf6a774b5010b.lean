-- Prove2me | Definitions.Def_SourceProof_7e3d78394bcbf6a774b5010b
-- name    : SourceProof_7e3d78394bcbf6a774b5010b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:23:44.872113+00:00
-- url     : https://prove2.me/theorems/9c211fb0-d4c1-50a8-8ec9-cce22670243e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_cutoff

import Definitions.Def_SourceProof_250eb65c80240d2467f59640
import Definitions.Def_SourceProof_3167c9529a23dc145fa8582c
import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_57c6cd02a544a4f092339b71
import Definitions.Def_SourceProof_6e9bb4c834a1b44d569cca8b
import Definitions.Def_SourceProof_8510e2a398f823aff8350c3b
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_9627c7bfbc6b93307efa4944
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_dfba211aff959c1cb4116abf
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_ebaf9e73dbb24b573c624591
import Definitions.Def_SourceProof_f2daf40b88ac8840065b16fc

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
theorem _root_.Prove2MeSourceProof.h_7e3d78394bcbf6a774b5010b
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Indistinguishable
      (hX.stochasticIntegral hF (_root_.Prove2MeSourceProof.h_dfba211aff959c1cb4116abf ha hτ) ((_root_.Prove2MeSourceProof.h_250eb65c80240d2467f59640 hr) τ))
      (MeasureTheory.stoppedProcess (hX.stochasticIntegral hF ha hr) τ) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  apply (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b hX) hF _ _
    (fun n ↦ (_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 (hS n)) hτ) ((_root_.Prove2MeSourceProof.h_57c6cd02a544a4f092339b71 huS) τ)
  · have heq : (fun n ↦ ((_root_.Prove2MeSourceProof.h_ebaf9e73dbb24b573c624591 (hS n)) hτ).elementaryIntegralProcess X) =
        fun n ↦ MeasureTheory.stoppedProcess ((hS n).elementaryIntegralProcess X) τ := by
      funext n
      exact (_root_.Prove2MeSourceProof.h_f2daf40b88ac8840065b16fc (hS n)) hτ X
    rw [heq]
    exact (_root_.Prove2MeSourceProof.h_6e9bb4c834a1b44d569cca8b ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS)) τ
  · exact (_root_.Prove2MeSourceProof.h_9127ba9e47e57c570411dae8 (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr))) τ
end IsSemimartingale

end ProbabilityTheory


