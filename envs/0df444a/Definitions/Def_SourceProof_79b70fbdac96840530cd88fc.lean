-- Prove2me | Definitions.Def_SourceProof_79b70fbdac96840530cd88fc
-- name    : SourceProof_79b70fbdac96840530cd88fc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:23:31.847751+00:00
-- url     : https://prove2.me/theorems/8d6f8069-2b24-5039-bae0-e0da830df14f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_congr_integrand

import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linearity and integrand invariance of the constructed integral

Identities are indistinguishability statements, not equality of arbitrary chosen
versions. Every identity follows from actual simple approximations and uniqueness.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H K : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_79b70fbdac96840530cd88fc
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) (hHK : Indistinguishable H K P) :
    Indistinguishable (hX.stochasticIntegral hF haH hrH)
      (hX.stochasticIntegral hF haK hrK) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd haH hF hrH
  exact (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b hX) hF haH hrH hS huS
    ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF haK hrK hS ((_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 huS) hHK))
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF haK hrK))
end IsSemimartingale

end ProbabilityTheory


