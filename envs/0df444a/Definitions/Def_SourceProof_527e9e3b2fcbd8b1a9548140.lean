-- Prove2me | Definitions.Def_SourceProof_527e9e3b2fcbd8b1a9548140
-- name    : SourceProof_527e9e3b2fcbd8b1a9548140
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:39.063471+00:00
-- url     : https://prove2.me/theorems/312316d5-25f9-40f1-811a-2c448a02d471
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.sum_weight_eq_sum_grid
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increasing enumeration of a finite family of times

`sortedGrid S` lists the elements of a finite set `S ⊆ ℝ` in increasing order at the indices
`1, …, #S`, and takes the value `0` at index `0` and beyond `#S`. When every element of `S` is
positive it is strictly increasing on `{0, …, #S}`.

A finite family of (coordinate, time) pairs carrying real weights is thereby rewritten as a sum
over such a grid: `posTimes` collects the strictly positive times of the family and `weightAt`
collects the weights sharing a coordinate and a time.
-/

namespace LevyStochCalc.Analysis

open Finset

variable (S : Finset ℝ)

variable {d : ℕ} {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_527e9e3b2fcbd8b1a9548140 (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ)
    (v : Fin d → ℝ → ℝ) (hv : ∀ p : F, (p.1.2 : ℝ) ≤ 0 → v p.1.1 (p.1.2 : ℝ) = 0)
    {S : Finset ℝ} (hS : posTimes F ⊆ S) (hSpos : ∀ x ∈ S, 0 < x) :
    ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) := by
  calc ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ p : F, (if (p.1.2 : ℝ) ∈ S then w p * v p.1.1 (p.1.2 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hpos : 0 < (p.1.2 : ℝ)
        · rw [if_pos (hS (LevyStochCalc.Analysis.mem_posTimes p.2 hpos))]
          exact mul_comm _ _
        · rw [if_neg fun hmem => absurd (hSpos _ hmem) hpos,
            hv p (not_lt.mp hpos), zero_mul]
    _ = ∑ p : F, ∑ x ∈ S,
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) :=
        Finset.sum_congr rfl fun p _ => (Finset.sum_ite_eq S ((p.1.2 : ℝ))
          fun _ => w p * v p.1.1 (p.1.2 : ℝ)).symm
    _ = ∑ x ∈ S, ∑ p : F,
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ x ∈ S, ∑ i, LevyStochCalc.Analysis.weightAt F w x i * v i x :=
        Finset.sum_congr rfl fun x _ => (LevyStochCalc.Analysis.sum_weightAt_mul F w v x).symm
    _ = ∑ k ∈ Finset.Ico 1 (S.card + 1), ∑ i,
          LevyStochCalc.Analysis.weightAt F w (LevyStochCalc.Analysis.sortedGrid S k) i * v i (LevyStochCalc.Analysis.sortedGrid S k) :=
        (LevyStochCalc.Analysis.sum_Ico_sortedGrid _ fun x => ∑ i, LevyStochCalc.Analysis.weightAt F w x i * v i x).symm
    _ = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          LevyStochCalc.Analysis.weightAt F w (LevyStochCalc.Analysis.sortedGrid S k) i * v i (LevyStochCalc.Analysis.sortedGrid S k) :=
        Finset.sum_comm
end LevyStochCalc.Analysis


