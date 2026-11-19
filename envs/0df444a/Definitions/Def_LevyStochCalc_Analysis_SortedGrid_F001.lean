-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F001
-- name    : LevyStochCalc_Analysis_SortedGrid_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:16:07.89905+00:00
-- url     : https://prove2.me/theorems/e96e3b31-9055-4d41-b971-603ed3809ec7
-- title:
--   Source declarations: LevyStochCalc.Analysis.SortedGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.SortedGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The last point of the sorted grid of a nonempty finite set belongs to it. -/
theorem sortedGrid_card_mem {S : Finset ℝ} (hS : S.Nonempty) : sortedGrid S S.card ∈ S := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by
    have : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega⟩
  have hns : n < S.card := by omega
  rw [hn]
  exact sortedGrid_succ_mem S hns
end LevyStochCalc.Analysis


