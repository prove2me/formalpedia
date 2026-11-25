-- Prove2me | Definitions.Def_SourceProof_f50de7c96dd83d69635d466a
-- name    : SourceProof_f50de7c96dd83d69635d466a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:52:15.009551+00:00
-- url     : https://prove2.me/theorems/f4bb525b-de69-5b8f-88de-c63ab4a3b4f5
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.exists_bounded_caglad_cutoffSequence

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_FirstExitTruncation_F000
import Definitions.Def_SourceProof_190b4be347a5022499cfb877
import Definitions.Def_SourceProof_601f22d91be529891e796a38
import Definitions.Def_SourceProof_877ba5ad1fd0d646fb6c666f
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_d40053975454af7beb3a1cf6
import Definitions.Def_SourceProof_d800562057b531429ad0976a
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded masked cutoffs of adapted caglad processes

Open norm exits need not attain their target. Compact path bounds prove divergence
without an attainment claim. The closed cutoff remains bounded at a positive exit
by left continuity; the initial mask handles arbitrary initial values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {H : ℝ≥0 → Ω → ℝ}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_f50de7c96dd83d69635d466a
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}
    (ha : Adapted F H) (hF : F.IsUsual P) (hr : HasCagladPaths H P) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence F τ P ∧ Monotone τ ∧
      ∀ n, ∀ᵐ ω ∂P, ∀ t, ‖{v | 0 < τ n v}.indicator (cutoffIntegrand H (τ n) t) ω‖ ≤ (n : ℝ) := by
  classical
  obtain ⟨K, heq, haK, hrK⟩ := (_root_.Prove2MeSourceProof.h_d800562057b531429ad0976a ha) hF hr
  let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ↦ hittingAfter K {x | (n : ℝ) < ‖x‖} 0
  have hmono : Monotone τ := fun _ _ hnm ↦ _root_.Prove2MeSourceProof.h_601f22d91be529891e796a38 (Nat.cast_le.mpr hnm)
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  refine ⟨τ, ⟨⟨fun n ↦ (_root_.Prove2MeSourceProof.h_877ba5ad1fd0d646fb6c666f haK)
    (fun ω ↦ (hrK ω).1) (isOpen_lt continuous_const continuous_norm) 0,
    ae_of_all _ fun ω ↦ (_root_.Prove2MeSourceProof.h_190b4be347a5022499cfb877 (hrK ω))⟩,
    ae_of_all _ fun _ _ _ hnm ↦ hmono hnm _⟩, hmono, ?_⟩
  intro n
  filter_upwards [heq] with ω hω t
  have he : ProbabilityTheory.cutoffIntegrand H (τ n) t ω = ProbabilityTheory.cutoffIntegrand K (τ n) t ω := by
    simp only [ProbabilityTheory.cutoffIntegrand, hω]
  by_cases hp : 0 < τ n ω
  · rw [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp), he]
    have hb := _root_.Prove2MeSourceProof.h_d40053975454af7beb3a1cf6 (Nat.cast_nonneg n) (hrK ω).1 t
    change ‖{v | 0 < τ n v}.indicator (ProbabilityTheory.cutoffIntegrand K (τ n) t) ω‖ ≤ (n : ℝ) at hb
    simpa only [indicator_of_mem (show ω ∈ {v | 0 < τ n v} from hp)] using hb
  · simpa only [indicator_of_notMem (show ω ∉ {v | 0 < τ n v} from hp), norm_zero]
      using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
end Adapted

end MeasureTheory


