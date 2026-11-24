-- Prove2me | Definitions.Def_SourceProof_8d231227f004d115d9169458
-- name    : SourceProof_8d231227f004d115d9169458
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:16.029799+00:00
-- url     : https://prove2.me/theorems/eeaa8a06-29f1-4ba6-9303-fe8f2a4cd56b
-- title:
--   StochLean source theorem: ProbabilityTheory.stoppingTime_rightGridFinite

import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_5a9e4b64f838761a6226e9d1

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Upper-grid approximations of finite stopping times

These generic helpers were originally used in the Brownian strong Markov
proof. They now live at the stopping-time owner so optional sampling and
localization reuse the same construction. Existing public names are retained.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_8d231227f004d115d9169458
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ (rightGrid n (τ ω) : WithTop ℝ≥0)) := by
  intro u
  let m : ℕ := n + 1
  have hm : (0 : ℝ≥0) < (m : ℝ≥0) := by positivity
  have hevent : {ω | (rightGrid n (τ ω) : WithTop ℝ≥0) ≤ u} =
      ⋃ k : {k : ℕ // (k : ℝ≥0) / m ≤ u},
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((k.1 : ℝ≥0) / m : ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h' : rightGrid n (τ ω) ≤ u := WithTop.coe_le_coe.mp h
      refine ⟨⟨Nat.ceil ((m : ℝ≥0) * τ ω), ?_⟩, ?_⟩
      · simpa only [m, rightGrid] using h'
      · exact_mod_cast _root_.Prove2MeSourceProof.h_5a9e4b64f838761a6226e9d1 n (τ ω)
    · rintro ⟨k, hk⟩
      have hk' : τ ω ≤ (k.1 : ℝ≥0) / m := WithTop.coe_le_coe.mp hk
      have hmul : (m : ℝ≥0) * τ ω ≤ k.1 := by
        have h := (le_div_iff₀ hm).mp hk'
        simpa [mul_comm] using h
      have hceil : Nat.ceil ((m : ℝ≥0) * τ ω) ≤ k.1 := Nat.ceil_le.mpr hmul
      apply WithTop.coe_le_coe.mpr
      calc
        rightGrid n (τ ω) =
            (Nat.ceil ((m : ℝ≥0) * τ ω) : ℝ≥0) / m := by rfl
        _ ≤ (k.1 : ℝ≥0) / m := by gcongr
        _ ≤ u := k.2
  rw [hevent]
  exact MeasurableSet.iUnion fun k ↦
    ℱ.mono k.2 _ (hτ ((k.1 : ℝ≥0) / m))
namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

end FiniteStoppingTime

end ProbabilityTheory


