-- Prove2me | Definitions.Def_SourceProof_0144d989fffae649e78e1206
-- name    : SourceProof_0144d989fffae649e78e1206
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:13:54.259862+00:00
-- url     : https://prove2.me/theorems/337e77f0-f02e-52e5-b9cd-6d21cdf9d9be
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.elementaryIntegralProcess_stochasticIntegral

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Associativity_F000
import Definitions.Def_SourceProof_13bd89c9f09633f52fbf30fb
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7ca5a4a340ad9cc180bba716
import Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a306c42680d425170aa442b0
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_ae584a9168b1bd16f954b4f8
import Definitions.Def_SourceProof_badb7657c0d57407ebcad38e
import Definitions.Def_SourceProof_bae5ae9701ba5ce704cf231a
import Definitions.Def_SourceProof_d0ba14a65d084d5914c41424
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_f2413a3b51825efc6a057b76
import Definitions.Def_SourceProof_fed1f541ebd11de35fc56705
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Associativity with a simple outer integrand

The inner integral is the actual Chapter II extension. Its semimartingale
property is not assumed here: this result is used to prove that property.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X G H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_0144d989fffae649e78e1206
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hG : IsSimplePredictable G F) (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Indistinguishable (hG.elementaryIntegralProcess (hX.stochasticIntegral hF ha hr))
      (hX.stochasticIntegral hF (fun t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 hG) t).mul (ha t))
        ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 hG) P)) hr)) P := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  have huJ := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  have huOuter := (_root_.Prove2MeSourceProof.h_13bd89c9f09633f52fbf30fb hG) hF
    (fun n ↦ (_root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a (hS n)) (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)))
    ((_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF ha hr)
    (fun n ↦ (_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 (hS n)) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
    ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr) huJ
  have huProd := (_root_.Prove2MeSourceProof.h_fed1f541ebd11de35fc56705 huS)
    (fun n t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (hS n)) t).mono (F.le t) le_rfl)
    (fun t ↦ (ha t).mono (F.le t) le_rfl)
    (fun t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 hG) t).mono (F.le t) le_rfl)
    (fun n ↦ (_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (hS n)) P) hr ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 hG) P)
  have huProdJ := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF
    (fun t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 hG) t).mul (ha t)) ((_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 hG) P)) hr)
    (fun n ↦ (_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) (hS n)) huProd
  have heq : (fun n ↦ hG.elementaryIntegralProcess ((hS n).elementaryIntegralProcess X)) =
      fun n ↦ ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 hG) (hS n)).elementaryIntegralProcess X := by
    funext n
    exact (_root_.Prove2MeSourceProof.h_badb7657c0d57407ebcad38e hG) (hS n) X
  rw [heq] at huOuter
  exact (_root_.Prove2MeSourceProof.h_ae584a9168b1bd16f954b4f8 huOuter) huProdJ
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 hG)
      ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr)))
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF _ _))
end IsSemimartingale

end ProbabilityTheory


