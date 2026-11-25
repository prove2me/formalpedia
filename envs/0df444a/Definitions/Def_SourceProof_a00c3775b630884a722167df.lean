-- Prove2me | Definitions.Def_SourceProof_a00c3775b630884a722167df
-- name    : SourceProof_a00c3775b630884a722167df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:23:43.286405+00:00
-- url     : https://prove2.me/theorems/d08b1655-97bb-5536-887f-eb188c6c116e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_indicator_integrand

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_InitialMask_F000
import Definitions.Def_SourceProof_18476b90b4b71a8ada4a076c
import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_538276c71aeae59150be9f02
import Definitions.Def_SourceProof_6ecb08b0ecac59b7f0cdb61a
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_ba15608e2ab7164b205d1611
import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_f5e68e551f95dbde3aa7e530

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Initial masks commute with the constructed stochastic integral

The source initial term is included in both identities. Combining the identities
with stopping gives the exact masked local-property convention.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_a00c3775b630884a722167df
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P)
    {s : Set Ω} (hs : MeasurableSet[F 0] s) :
    Indistinguishable
      (hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 ha) hs) ((_root_.Prove2MeSourceProof.h_d93b464447ac66fa122a70c4 hr) s))
      (fun t ↦ s.indicator (hX.stochasticIntegral hF ha hr t)) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  apply (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b hX) hF _ _
    (fun n ↦ (_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 (hS n)) hs) ((_root_.Prove2MeSourceProof.h_538276c71aeae59150be9f02 huS) s)
  · have heq : (fun n ↦ ((_root_.Prove2MeSourceProof.h_ba15608e2ab7164b205d1611 (hS n)) hs).elementaryIntegralProcess X) =
        fun n t ↦ s.indicator ((hS n).elementaryIntegralProcess X t) := by
      funext n
      exact (_root_.Prove2MeSourceProof.h_18476b90b4b71a8ada4a076c (hS n)) hs X
    rw [heq]
    exact (_root_.Prove2MeSourceProof.h_538276c71aeae59150be9f02 ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS)) s
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr)) s))
end IsSemimartingale

end ProbabilityTheory


