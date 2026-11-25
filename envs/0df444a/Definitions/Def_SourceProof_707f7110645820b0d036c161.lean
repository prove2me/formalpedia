-- Prove2me | Definitions.Def_SourceProof_707f7110645820b0d036c161
-- name    : SourceProof_707f7110645820b0d036c161
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:28:26.489604+00:00
-- url     : https://prove2.me/theorems/db984a9d-aa50-4f3f-9fc5-971d9e3b6b7f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_sub_integrator

import Definitions.Def_SourceProof_042946cfff92727bdbde6373
import Definitions.Def_SourceProof_34df0ff9749e9285f8ed730b
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_63e1469ea21d6ee826860dba
import Definitions.Def_SourceProof_76e6f1c00540bd94935e0dc0
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_d0e331387f6701b34b2c711d
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linearity of the constructed integral in the semimartingale integrator

Every identity compares the existing canonical selectors by indistinguishability.
One common simple approximation suffices for both integrators; no convergence
of arbitrary varying semimartingales is asserted.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_707f7110645820b0d036c161
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) hY).stochasticIntegral hF ha hr)
      (hX.stochasticIntegral hF ha hr - hY.stochasticIntegral hF ha hr) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  apply (_root_.Prove2MeSourceProof.h_34df0ff9749e9285f8ed730b ((_root_.Prove2MeSourceProof.h_63e1469ea21d6ee826860dba hX) hY)) hF ha hr hS huS
  · have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS))
      ((_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hY) hF ha hr hS huS)
    simpa only [_root_.Prove2MeSourceProof.h_042946cfff92727bdbde6373] using hu
  · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr))
      ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hY) hF ha hr)))
end IsSemimartingale

end ProbabilityTheory


