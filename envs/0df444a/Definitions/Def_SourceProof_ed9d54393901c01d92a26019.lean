-- Prove2me | Definitions.Def_SourceProof_ed9d54393901c01d92a26019
-- name    : SourceProof_ed9d54393901c01d92a26019
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:05.926533+00:00
-- url     : https://prove2.me/theorems/b2d08161-3d4a-404c-8ea4-2ed36dfb9d3a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsGoodIntegrator.const_mul

import Definitions.Def_StochLean_Probability_Process_Semimartingale_Basic_F001
import Definitions.Def_SourceProof_11d1e52ae792291cfc25906e
import Definitions.Def_SourceProof_91776c6d66e3ec9a393c48f3
import Definitions.Def_SourceProof_f4d8a21bf210a12aba5a0fa0
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Linear stability of the source good-integrator predicate

These results use elementary integration and its quantitative continuity
criterion. No classical decomposition or Bichteler-Dellacherie theorem is
assumed in proving stability.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsGoodIntegrator
theorem _root_.Prove2MeSourceProof.h_ed9d54393901c01d92a26019 (hX : IsGoodIntegrator X F P) (c : ℝ) :
    IsGoodIntegrator (fun t ω ↦ c * X t ω) F P := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul]
    exact _root_.Prove2MeSourceProof.h_f4d8a21bf210a12aba5a0fa0 F P
  apply _root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mpr
  intro ε hε η hη
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨δ, hδ, hb⟩ := (_root_.Prove2MeSourceProof.h_91776c6d66e3ec9a393c48f3.mp hX)
    (ε / ‖c‖) (div_pos hε hcpos) η hη
  refine ⟨δ, hδ, fun H hH hbound ↦ ?_⟩
  rw [(_root_.Prove2MeSourceProof.h_11d1e52ae792291cfc25906e hH)]
  apply (measure_mono (show {ω | ε ≤ ‖c * hH.elementaryIntegral X ω‖} ⊆
      {ω | ε / ‖c‖ ≤ ‖hH.elementaryIntegral X ω‖} from ?_)).trans (hb H hH hbound)
  intro ω hω
  change ε ≤ ‖c * hH.elementaryIntegral X ω‖ at hω
  change ε / ‖c‖ ≤ ‖hH.elementaryIntegral X ω‖
  rw [div_le_iff₀ hcpos]
  simpa only [norm_mul, mul_comm] using hω
end IsGoodIntegrator

end ProbabilityTheory


