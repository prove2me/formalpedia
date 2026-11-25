-- Prove2me | Definitions.Def_SourceProof_3e1f2415255d4696a3db025d
-- name    : SourceProof_3e1f2415255d4696a3db025d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:07:06.422045+00:00
-- url     : https://prove2.me/theorems/d3c92887-0b18-48ba-8fe3-9fa199a4f1fb
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.exists_bounded_stoppingSequence

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Continuous_F000
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_541913de150c81e147df976a
import Definitions.Def_SourceProof_54ebcd041cff466afc2e0a1a
import Definitions.Def_SourceProof_9127ba9e47e57c570411dae8
import Definitions.Def_SourceProof_96c0d23ed76988d7c3d3ef45
import Definitions.Def_SourceProof_9b3b467d9208979297cd6213
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_d01ba5ff5c179dcd321a94d0
import Definitions.Def_SourceProof_f87513931c8b2e5853f4c459
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded stopping sequences for continuous adapted processes

This construction requires no martingale or integrability assumption. It is the shared
path/stopping ingredient for localization both at infinity and up to a random lifetime.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_3e1f2415255d4696a3db025d
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Adapted F X) (hF : F.IsUsual P) (hcont : HasContinuousPaths X P)
    (C : ℝ≥0) (hzero : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ C) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsPreLocalizingSequence F τ P ∧ Monotone τ ∧
      ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖stoppedProcess X (τ n) t ω‖ ≤ (C : ℝ) + n := by
  obtain ⟨Y, heq, hprog, hc⟩ :=
    (_root_.Prove2MeSourceProof.h_d01ba5ff5c179dcd321a94d0 hX.stronglyAdapted) hF hcont
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter Y {x | (C : ℝ) + n ≤ |x|} 0
  have hτ : ∀ n, IsStoppingTime F (τ n) := fun n ↦
    (_root_.Prove2MeSourceProof.h_541913de150c81e147df976a hprog.stronglyAdapted.adapted) hc _
  have hmono : Monotone τ := by
    intro n m hnm ω
    exact _root_.Prove2MeSourceProof.h_54ebcd041cff466afc2e0a1a (hc ω) (add_le_add le_rfl (Nat.cast_le.mpr hnm))
  have htop : ∀ ω, Tendsto (τ · ω) atTop (𝓝 ⊤) := by
    intro ω
    apply tendsto_nhds_top_mono' (_root_.Prove2MeSourceProof.h_f87513931c8b2e5853f4c459 (hc ω))
    intro n
    exact _root_.Prove2MeSourceProof.h_54ebcd041cff466afc2e0a1a (hc ω) (le_add_of_nonneg_left C.coe_nonneg)
  refine ⟨τ, ⟨hτ, ae_of_all _ htop⟩, hmono, fun n ↦ ?_⟩
  filter_upwards [(_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 heq) (τ n), heq, hzero] with ω hstop hω hz t
  rw [hstop t, Real.norm_eq_abs]
  apply _root_.Prove2MeSourceProof.h_9b3b467d9208979297cd6213 (hc ω)
  rw [← hω 0, ← Real.norm_eq_abs]
  exact hz.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
end Adapted

end MeasureTheory


