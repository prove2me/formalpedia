-- Prove2me | Definitions.Def_SourceProof_e2b6e4c8b89a0b17690a85de
-- name    : SourceProof_e2b6e4c8b89a0b17690a85de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:18.476678+00:00
-- url     : https://prove2.me/theorems/f39aad39-ccb8-5cb7-b26d-26b72da87976
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.uniformIntegrable_bounded_stoppedValue

import Definitions.Def_SourceProof_1aa8fa3c0942e35b7eee3422
import Definitions.Def_SourceProof_abd730752414d0d67e6d98a8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform integrability under continuous-time stopping

Every bounded stopping value of a closed martingale is a conditional
expectation of its closing variable. Their union over all finite bounds is
therefore UI. Taking AE limits gives the same result for arbitrary families
of AE-finite stopping times. In particular Protter I.18 follows without
assigning an artificial terminal value on the event that a stopping time is
infinite: all coordinates of a stopped process are evaluated at finite times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_e2b6e4c8b89a0b17690a85de {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hprog : IsStronglyProgressive F X) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hb : ∀ i, ∃ T : ℝ≥0, ∀ ω, τ i ω ≤ T) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  obtain ⟨Z, hi, hc⟩ := (_root_.Prove2MeSourceProof.h_1aa8fa3c0942e35b7eee3422 hX) hu
  apply (hi.uniformIntegrable_condExp (fun i ↦ (hτ i).measurableSpace_le)).ae_eq
  intro i
  obtain ⟨T, hT⟩ := hb i
  exact (((_root_.Prove2MeSourceProof.h_abd730752414d0d67e6d98a8 hX) hprog hr (hτ i) hT).trans
    ((condExp_congr_ae (hc T)).trans (condExp_condExp_of_le
      ((hτ i).measurableSpace_le_of_le_const hT) (F.le T)))).symm
end MeasureTheory.Martingale

namespace ProbabilityTheory.IsUIMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

end ProbabilityTheory.IsUIMartingale


