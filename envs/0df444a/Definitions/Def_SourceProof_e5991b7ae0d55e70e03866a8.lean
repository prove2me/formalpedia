-- Prove2me | Definitions.Def_SourceProof_e5991b7ae0d55e70e03866a8
-- name    : SourceProof_e5991b7ae0d55e70e03866a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:22:32.248219+00:00
-- url     : https://prove2.me/theorems/b670af68-364a-4cbe-a3f6-aa36143e70f7
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.iUnion_timeSlab
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh

theorem _root_.Prove2MeSourceProof.h_e5991b7ae0d55e70e03866a8 (n : ℕ) : (⋃ k : ℕ, timeSlab n k) = Set.Ioi (0 : ℝ) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  ext x
  simp only [Set.mem_iUnion, LevyStochCalc.Poisson.timeSlab, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk1, -⟩
    exact lt_of_le_of_lt (by positivity) hk1
  · intro hx
    have hy : (0 : ℝ) < x * 2 ^ n := by positivity
    set m : ℕ := ⌈x * 2 ^ n⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_ceil_iff.mpr hy
    refine ⟨m - 1, ?_, ?_⟩
    · rw [div_lt_iff₀ hpow]
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
      rw [hcast]
      have := Nat.ceil_lt_add_one hy.le
      rw [← hm] at this
      linarith
    · rw [le_div_iff₀ hpow]
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
        ring
      rw [hcast, hm]
      exact Nat.le_ceil _
end Mesh

section Simple

end Simple

end LevyStochCalc.Poisson


