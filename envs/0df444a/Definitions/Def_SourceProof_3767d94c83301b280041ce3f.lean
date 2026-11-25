-- Prove2me | Definitions.Def_SourceProof_3767d94c83301b280041ce3f
-- name    : SourceProof_3767d94c83301b280041ce3f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:43:20.013783+00:00
-- url     : https://prove2.me/theorems/fdbb22a4-fd84-5a9b-83a4-08c82eecc288
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_stochasticIntegral

import Definitions.Def_SourceProof_0144d989fffae649e78e1206
import Definitions.Def_SourceProof_3ad31bfe6f0351b15e1222d2
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_615a61300ee6a9f8d8759333
import Definitions.Def_SourceProof_7ca5a4a340ad9cc180bba716
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_ae584a9168b1bd16f954b4f8
import Definitions.Def_SourceProof_d0ba14a65d084d5914c41424
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.19: associativity on the Chapter II domain

Both adapted integrands have common-event caglad paths. The inner integral is
proved to be a semimartingale before the outer general integral is selected.
Associativity is an indistinguishability identity, including its initial term.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X G H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3767d94c83301b280041ce3f
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haG : Adapted F G) (hrG : HasCagladPaths G P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P) :
    Indistinguishable
      (((_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF haH hrH).stochasticIntegral hF haG hrG)
      (hX.stochasticIntegral hF (fun t ↦ (haG t).mul (haH t)) ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hrG) hrH)) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd haG hF hrG
  have hY := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF haH hrH
  have huLeft := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hY) hF haG hrG hS huS
  have huProduct := (_root_.Prove2MeSourceProof.h_615a61300ee6a9f8d8759333 huS)
    (fun n t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (hS n)) t).mono (F.le t) le_rfl)
    (fun t ↦ (haG t).mono (F.le t) le_rfl)
    (fun t ↦ (haH t).mono (F.le t) le_rfl)
    (fun n ↦ (_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (hS n)) P) hrG hrH
  have huRight := (_root_.Prove2MeSourceProof.h_3ad31bfe6f0351b15e1222d2 hX) hF
    (fun t ↦ (haG t).mul (haH t)) ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 hrG) hrH)
    (fun n t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (hS n)) t).mul (haH t))
    (fun n ↦ (_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (hS n)) P)) hrH) huProduct
  have huIdentified := (_root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db huLeft) (fun n ↦
    (_root_.Prove2MeSourceProof.h_0144d989fffae649e78e1206 hX) hF (hS n) haH hrH)
  exact (_root_.Prove2MeSourceProof.h_ae584a9168b1bd16f954b4f8 huIdentified) huRight
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hY) hF haG hrG))
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF _ _))
end IsSemimartingale

end ProbabilityTheory


