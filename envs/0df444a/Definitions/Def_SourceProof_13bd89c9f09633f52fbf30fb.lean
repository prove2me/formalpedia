-- Prove2me | Definitions.Def_SourceProof_13bd89c9f09633f52fbf30fb
-- name    : SourceProof_13bd89c9f09633f52fbf30fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:45.326937+00:00
-- url     : https://prove2.me/theorems/4e960587-7789-4e04-b210-663e1bcc0e24
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.tendstoUCP_elementaryIntegralProcess_integrator

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_43fbf96de532b2e4c5ed2cd2
import Definitions.Def_SourceProof_790b2f2d9706f0b80ab186f4
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a307e422895411519841ce97
import Definitions.Def_SourceProof_bae5ae9701ba5ce704cf231a
import Definitions.Def_SourceProof_ee4e1738437f392088834bc8
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuity in the integrator for a fixed elementary integrand

Only finitely many stopped increments are involved. No semimartingale premise
on the integrators, coefficient bound, or coefficient integrability is used.
This does not assert continuity in a varying integrator for general integrands.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_13bd89c9f09633f52fbf30fb
    [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (hF : F.IsUsual P) (haX : ∀ n, Adapted F (X n)) (haY : Adapted F Y)
    (hrX : ∀ n, HasCadlagPaths (X n) P) (hrY : HasCadlagPaths Y P)
    (hu : TendstoUCP P X atTop Y) :
    TendstoUCP P (fun n ↦ hH.elementaryIntegralProcess (X n)) atTop
      (hH.elementaryIntegralProcess Y) := by
  apply _root_.Prove2MeSourceProof.h_43fbf96de532b2e4c5ed2cd2
    (fun n T ↦ _root_.Prove2MeSourceProof.h_790b2f2d9706f0b80ab186f4
      (fun t ↦ (((_root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a hH) (haX n) hF
        (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (hrX n))) t).mono (F.le t) le_rfl)
      (fun t ↦ (((_root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a hH) haY hF
        (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hrY)) t).mono (F.le t) le_rfl)
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 hH) (hrX n)))
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 hH) hrY)) T)
  intro ns hns
  obtain ⟨k, _, hk⟩ := (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_a307e422895411519841ce97 hu) hns))
  refine ⟨k, hk.mono fun ω hω T ↦ ?_⟩
  apply _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mpr
  exact (_root_.Prove2MeSourceProof.h_ee4e1738437f392088834bc8 hH.choose)
    (_root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hω T))
end IsSimplePredictable

end ProbabilityTheory


