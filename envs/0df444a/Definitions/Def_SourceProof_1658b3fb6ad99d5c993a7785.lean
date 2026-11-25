-- Prove2me | Definitions.Def_SourceProof_1658b3fb6ad99d5c993a7785
-- name    : SourceProof_1658b3fb6ad99d5c993a7785
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:52:34.082086+00:00
-- url     : https://prove2.me/theorems/25dc11ad-6678-47ef-83df-53319bff8f49
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_bounded_simplePredictable_tendstoUCP

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Definitions.Def_SourceProof_51267744f3c51c8bf8b4f2ca
import Definitions.Def_SourceProof_793c38bcb4aaed48eefedcc7
import Definitions.Def_SourceProof_98ebe068ef5b612c5efe473d
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_b9f27f4688790c8c7a3c070b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded simple approximation with the original bound

Scalar interval projection fixes zero, so it preserves the full source simple
class. Its nonexpansiveness retains UCP convergence. The input bound may hold
only on one full-measure path event; every approximant is bounded everywhere.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_1658b3fb6ad99d5c993a7785 [IsFiniteMeasure P]
    (ha : Adapted F H) (hF : F.IsUsual P) (hr : HasCagladPaths H P)
    (C : ℝ≥0) (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧
      (∀ n t ω, ‖S n t ω‖ ≤ C) ∧ TendstoUCP P S atTop H := by
  obtain ⟨A, hA, huA⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  let f : ℝ → ℝ := fun x ↦ max (-(C : ℝ)) (min (C : ℝ) x)
  have hf : LipschitzWith 1 f := (LipschitzWith.id.const_min (C : ℝ)).const_max (-(C : ℝ))
  refine ⟨fun n t ω ↦ f (A n t ω), fun n ↦ (_root_.Prove2MeSourceProof.h_b9f27f4688790c8c7a3c070b (hA n)) C,
    fun n t ω ↦ _root_.Prove2MeSourceProof.h_51267744f3c51c8bf8b4f2ca C (A n t ω), ?_⟩
  apply (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 ((_root_.Prove2MeSourceProof.h_98ebe068ef5b612c5efe473d huA) hf))
  exact hb.mono fun ω hω t ↦ _root_.Prove2MeSourceProof.h_793c38bcb4aaed48eefedcc7 (hω t)
end ProbabilityTheory


