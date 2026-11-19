-- Prove2me | Definitions.Def_SourceProof_7ea79b056610f3e15dd559e8
-- name    : SourceProof_7ea79b056610f3e15dd559e8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:49.707801+00:00
-- url     : https://prove2.me/theorems/561e0d8e-a495-492c-8e9e-4b3e1a035602
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.le_sortedGrid_card
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


theorem _root_.Prove2MeSourceProof.h_7ea79b056610f3e15dd559e8 {S : Finset ℝ} {x : ℝ} (hx : x ∈ S) :
    x ≤ sortedGrid S S.card := by
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  set n := S.card - 1 with hn
  have hcard : S.card = n + 1 := by omega
  have hns : n < S.card := by omega
  have hgrid : LevyStochCalc.Analysis.sortedGrid S S.card = S.orderEmbOfFin rfl ⟨n, hns⟩ := by
    conv_lhs => rw [hcard]
    exact LevyStochCalc.Analysis.sortedGrid_succ_of_lt S hns
  rw [hgrid]
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, S.orderEmbOfFin rfl j = x := by
    have hmem : x ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    exact hmem
  rw [← hj]
  have hjle : (j : ℕ) ≤ n := by
    have := j.isLt
    omega
  exact (S.orderEmbOfFin rfl).monotone (Fin.le_def.mpr hjle)
end LevyStochCalc.Analysis


