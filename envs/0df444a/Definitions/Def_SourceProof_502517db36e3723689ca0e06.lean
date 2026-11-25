-- Prove2me | Definitions.Def_SourceProof_502517db36e3723689ca0e06
-- name    : SourceProof_502517db36e3723689ca0e06
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:43.116798+00:00
-- url     : https://prove2.me/theorems/1542f16c-e230-5431-a0e1-3fefa4f278bf
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticVariationSumProcess_eq_square_sub_riemann

import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
import Definitions.Def_SourceProof_e1f3ecca529106853c30fa13
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw square-increment sums on stopping-time partitions

The pure deterministic square-sum owner is reused pathwise. The source initial
square is added exactly once. The telescoping identity is valid for arbitrary
real paths and repeated endpoints; no regularity hypothesis is required.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_502517db36e3723689ca0e06 (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    π.quadraticVariationSumProcess X t ω =
      (X (min (π.terminal ω) t) ω) ^ 2 - 2 * π.leftRiemannSumProcess X X t ω := by
  let ρ := π.path ω
  have htel := (_root_.Prove2MeSourceProof.h_e1f3ecca529106853c30fa13 ρ) (fun u ↦ (X (min u t) ω) ^ 2)
  simp only [StochLean.TimePartition.increment, zero_min] at htel
  have hcell (i : Fin π.size) :
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2 =
      (X (min (π.point i.succ ω) t) ω) ^ 2 -
        (X (min (π.point i.castSucc ω) t) ω) ^ 2 -
      2 * (X (π.point i.castSucc ω) ω *
        (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω)) := by
    by_cases hi : π.point i.castSucc ω ≤ t
    · rw [min_eq_left hi]
      ring
    · have ht : t ≤ π.point i.castSucc ω := (lt_of_not_ge hi).le
      have htr : t ≤ π.point i.succ ω := ht.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 ρ) i)
      simp only [min_eq_right ht, min_eq_right htr, sub_self, zero_pow (by norm_num : 2 ≠ 0),
        mul_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ ↦ hcell i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  change (∑ i : Fin π.size,
    ((X (min (π.point i.succ ω) t) ω) ^ 2 -
      (X (min (π.point i.castSucc ω) t) ω) ^ 2)) = _ at htel
  rw [htel] at hs
  change (X 0 ω) ^ 2 + (∑ i : Fin π.size,
    (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) = _
  rw [hs]
  change _ = _ - 2 * (∑ i : Fin π.size, _)
  ring
end ProbabilityTheory.StoppingTimePartition


