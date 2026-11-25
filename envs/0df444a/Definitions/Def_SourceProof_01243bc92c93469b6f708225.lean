-- Prove2me | Definitions.Def_SourceProof_01243bc92c93469b6f708225
-- name    : SourceProof_01243bc92c93469b6f708225
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:19.527649+00:00
-- url     : https://prove2.me/theorems/feb72fe8-bf59-4364-a130-6b6c742ab02a
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.jumpMeasure_eq_of_exponent_eq

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5
import Definitions.Def_SourceProof_b879bbcf8c2ae9203fc06819
import Definitions.Def_SourceProof_c76a94657b4085a094543e61
import Definitions.Def_SourceProof_ce1f5b736b8d388c0b16537f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_01243bc92c93469b6f708225 {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.jumpMeasure = ξ.jumpMeasure := by
  apply Measure.ext
  intro A hA
  let B : ℕ → Set ℝ := fun n => A ∩ ProbabilityTheory.LevyTriplet.levyIdentificationSet n
  have hBmono : Monotone B := by
    intro n m hnm x hx
    exact ⟨hx.1, _root_.Prove2MeSourceProof.h_b879bbcf8c2ae9203fc06819 hnm hx.2⟩
  have hB_eq (n : ℕ) : η.jumpMeasure (B n) = ξ.jumpMeasure (B n) := by
    have hr := congrArg (fun m : Measure ℝ => m A)
      (_root_.Prove2MeSourceProof.h_c76a94657b4085a094543e61 h n)
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA] at hr
    exact hr
  have hη := tendsto_measure_iUnion_atTop (μ := η.jumpMeasure) hBmono
  have hξ := tendsto_measure_iUnion_atTop (μ := ξ.jumpMeasure) hBmono
  have hseq : (η.jumpMeasure ∘ B) = (ξ.jumpMeasure ∘ B) := by
    funext n
    exact hB_eq n
  rw [hseq] at hη
  have hlimit := tendsto_nhds_unique hη hξ
  have hBunion : (⋃ n, B n) = A \ {0} := by
    calc
      (⋃ n, B n) = A ∩ ⋃ n, ProbabilityTheory.LevyTriplet.levyIdentificationSet n := by
        ext x
        simp only [B, Set.mem_iUnion, Set.mem_inter_iff]
        aesop
      _ = A ∩ {0}ᶜ := by rw [_root_.Prove2MeSourceProof.h_ce1f5b736b8d388c0b16537f]
      _ = A \ {0} := rfl
  have hηzero : η.jumpMeasure ({0} : Set ℝ) = 0 :=
    (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 η.isLevyMeasure_jumpMeasure)
  have hξzero : ξ.jumpMeasure ({0} : Set ℝ) = 0 :=
    (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 ξ.isLevyMeasure_jumpMeasure)
  rw [hBunion, measure_sdiff_null (s := A) hηzero,
    measure_sdiff_null (s := A) hξzero] at hlimit
  exact hlimit
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


