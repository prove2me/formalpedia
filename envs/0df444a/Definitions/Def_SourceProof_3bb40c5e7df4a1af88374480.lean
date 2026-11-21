-- Prove2me | Definitions.Def_SourceProof_3bb40c5e7df4a1af88374480
-- name    : SourceProof_3bb40c5e7df4a1af88374480
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:58:41.68529+00:00
-- url     : https://prove2.me/theorems/8883835b-14ad-4b9e-892f-5b137131abda
-- title:
--   LevyStochCalc source module: SourceProof_3bb40c5e7df4a1af88374480
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.sum_tail_mul_sub` comes from the `LevyStochCalc.Brownian.PRPGrid` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation over a grid

Iterating the one-window statement over the cells of a grid: a square-integrable weight of mean
zero and orthogonal to every Itô integral is orthogonal to every character of the increments of a
Brownian motion along a grid.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Grid

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Grid

section Abel


theorem _root_.Prove2MeSourceProof.h_3bb40c5e7df4a1af88374480 (c : ℕ → ℝ) {Wv : ℕ → ℝ} (h0 : Wv 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
      = ∑ k ∈ Finset.Ico 1 (n + 1), c k * Wv k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : ∀ k ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.Ico (k + 1) (n + 2), c j) * (Wv (k + 1) - Wv k)
            = (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
              + c (n + 1) * (Wv (k + 1) - Wv k) := by
        intro k hk
        have hk' : k + 1 ≤ n + 1 := Finset.mem_range.mp hk
        rw [Finset.sum_Ico_succ_top hk', add_mul]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hlast : ∑ k ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
          = ∑ k ∈ Finset.range n,
            (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k) := by
        rw [Finset.sum_range_succ]
        simp
      have htel : ∑ k ∈ Finset.range (n + 1), c (n + 1) * (Wv (k + 1) - Wv k)
          = c (n + 1) * Wv (n + 1) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub, h0, sub_zero]
      rw [hlast, ih, htel]
      exact (Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1) _).symm
end Abel

section Values

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

end Values

end LevyStochCalc.Brownian.Ito


