-- Prove2me | Definitions.Def_SourceProof_521bf039082cd15fcfae08ee
-- name    : SourceProof_521bf039082cd15fcfae08ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:22:11.273971+00:00
-- url     : https://prove2.me/theorems/e93eefc6-4f06-4db3-8f82-fd72974b4daa
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.pairwiseDisjoint_timeSlab
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

theorem _root_.Prove2MeSourceProof.h_521bf039082cd15fcfae08ee (n : ℕ) :
    Pairwise (Function.onFun Disjoint (timeSlab n)) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have key : ∀ i j : ℕ, i < j → Disjoint (LevyStochCalc.Poisson.timeSlab n i) (LevyStochCalc.Poisson.timeSlab n j) := by
    intro i j h
    have hij : ((i : ℝ) + 1) / 2 ^ n ≤ (j : ℝ) / 2 ^ n := by
      have hnum : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      gcongr
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    exact absurd (lt_of_le_of_lt (le_trans hxi.2 hij) hxj.1) (lt_irrefl _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm
end Mesh

section Simple

end Simple

end LevyStochCalc.Poisson


