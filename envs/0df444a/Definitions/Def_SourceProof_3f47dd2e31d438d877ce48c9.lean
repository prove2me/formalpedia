-- Prove2me | Definitions.Def_SourceProof_3f47dd2e31d438d877ce48c9
-- name    : SourceProof_3f47dd2e31d438d877ce48c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:28:44.572771+00:00
-- url     : https://prove2.me/theorems/3bf894f2-5408-4916-b865-1bf20e22d83e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_congr_integrator

import Definitions.Def_SourceProof_0fef2f232d2bf1adcaa99445
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Invariance of the constructed integral under indistinguishable integrators

A common simple approximation works for both integrators. Its integral processes
are indistinguishable, and UCP uniqueness identifies the two constructed limits.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3f47dd2e31d438d877ce48c9
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (hXY : Indistinguishable X Y P) :
    Indistinguishable (hX.stochasticIntegral hF ha hr) (hY.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  apply (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b hX) hF ha hr hS huS
  · exact (_root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hY) hF ha hr hS huS))
      (fun n ↦ (_root_.Prove2MeSourceProof.h_0fef2f232d2bf1adcaa99445 (hS n)) (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 hXY))
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hY) hF ha hr))
end IsSemimartingale

end ProbabilityTheory


