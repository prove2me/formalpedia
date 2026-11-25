-- Prove2me | Definitions.Def_SourceProof_62aa9c78f78fd9c67ea0fbce
-- name    : SourceProof_62aa9c78f78fd9c67ea0fbce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:21.826892+00:00
-- url     : https://prove2.me/theorems/cbf97f71-4fc9-47e1-a846-f1d4c15f32b5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tsum_largeJumpSequence_indicator_eq_tsum_Ioc

import Definitions.Def_StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000
import Definitions.Def_SourceProof_16b415d0c40536c6ca3b78ee
import Definitions.Def_SourceProof_1e736ec71ed59f8f581416d9
import Definitions.Def_SourceProof_74a6d27af8d8dbe7c2f7b734
import Definitions.Def_SourceProof_938ce1371f46ced800f20c31
import Definitions.Def_SourceProof_b54ddf128850614ab86e8113
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual large-jump sums through the existing lifetime enumeration

The canonical large-jump sequence escapes each finite horizon. Consequently
only finitely many of its closed steps are active by that horizon, and their
actual coefficient series is summable. Unique finite lifetimes and complete
large-jump coverage reindex this series as the literal positive-time jump sum.

An arbitrary real transformation is allowed at each jump. In particular, no
zero-preservation condition is imposed: the lifetime indicator remains outside
the transformation, so an infinite lifetime never contributes a finite-time
term, even when the transformation is nonzero at zero. Signed and norm sums
are the identity and norm specializations of the same result.

Adaptedness follows from the existing stopped-jump measurability and native
measurability of a countable sum. No new process, sum, or sampling owner is
introduced, and no integrability or jump-count moment is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

namespace IsCadlagPath

theorem _root_.Prove2MeSourceProof.h_62aa9c78f78fd9c67ea0fbce
    (hX : IsCadlagPath (X · ω)) (hb : 0 < b) (φ : ℝ → ℝ) (T : ℝ≥0) :
    (∑' n : ℕ, {v | largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)}.indicator
      (fun v ↦ φ (stoppedValueWithTerminal (jumpProcess X) (fun _ ↦ (0 : ℝ))
        (largeJumpSequence X b n) v)) ω) =
      ∑' s : Ioc 0 T, if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0 := by
  classical
  symm
  rw [tsum_subtype (Ioc 0 T)
    (fun s ↦ if b < ‖ProbabilityTheory.jumpProcess X s ω‖ then φ (ProbabilityTheory.jumpProcess X s ω) else 0)]
  apply _root_.Prove2MeSourceProof.h_74a6d27af8d8dbe7c2f7b734
    (τ := fun n ↦ ProbabilityTheory.largeJumpSequence X b n ω)
  · intro i j t hi hj
    have hjfin : ProbabilityTheory.largeJumpSequence X b j ω ≠ ⊤ := hj ▸ WithTop.coe_ne_top
    exact ((_root_.Prove2MeSourceProof.h_1e736ec71ed59f8f581416d9 hX) hb hjfin).mp (hi.trans hj.symm)
  · intro i hi
    apply indicator_of_notMem
    change ¬ ProbabilityTheory.largeJumpSequence X b i ω ≤ (T : WithTop ℝ≥0)
    rw [hi]
    exact WithTop.not_top_le_coe T
  · intro i t hi
    have ht := (_root_.Prove2MeSourceProof.h_b54ddf128850614ab86e8113 hX) hb hi
    simp only [indicator_apply, mem_ofPred_eq, mem_Ioc]
    rw [_root_.Prove2MeSourceProof.h_16b415d0c40536c6ca3b78ee hi]
    simp only [hi, WithTop.coe_le_coe, ht.1, ht.2, true_and, if_true]
  · intro t ht
    have hmem : t ∈ Ioc 0 T := by
      by_contra h
      exact ht (indicator_of_notMem h _)
    have hj : b < ‖ProbabilityTheory.jumpProcess X t ω‖ := by
      by_contra h
      rw [indicator_of_mem hmem, if_neg h] at ht
      exact ht rfl
    exact (_root_.Prove2MeSourceProof.h_938ce1371f46ced800f20c31 hX) hb hmem.1 hj
end IsCadlagPath

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

end MeasureTheory


