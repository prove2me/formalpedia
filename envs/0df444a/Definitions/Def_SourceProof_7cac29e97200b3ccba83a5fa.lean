-- Prove2me | Definitions.Def_SourceProof_7cac29e97200b3ccba83a5fa
-- name    : SourceProof_7cac29e97200b3ccba83a5fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:07:40.376235+00:00
-- url     : https://prove2.me/theorems/fc4ce7d0-3cd2-49ab-8091-3a76a3979dfc
-- title:
--   LevyStochCalc source module: SourceProof_7cac29e97200b3ccba83a5fa
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc` comes from the `LevyStochCalc.Brownian.ItoIncrementMomentRestrict` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Restriction of a simple predictable integrand to `(a, b]`

An adapted simple integrand `G` multiplied by the simple integrand `1_{(a, b]}` on their common
refinement is again an adapted simple integrand: its evaluation is `1_{(a, b]}·G`, its
coefficients vanish on every tile not contained in `(a, b]` and stay bounded by any bound on the
coefficients of `G`, and the variance budget of that per-tile bound is at most `C²(b − a)`.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_7cac29e97200b3ccba83a5fa {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
    (hab : a ≤ b) :
    H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
        H.N ≤ C ^ 2 * (b - a) := by
  classical
  set F : ℕ → ℝ := fun k =>
    min b (max a (H.partition ⟨min k H.N, Nat.lt_succ_of_le (min_le_right _ _)⟩)) with hFdef
  have hFmono : ∀ k, F k ≤ F (k + 1) := by
    intro k
    refine min_le_min le_rfl (max_le_max le_rfl (H.partition_strictMono.monotone ?_))
    rw [Fin.le_def]
    simp only
    omega
  have hFval : ∀ (j : ℕ) (hj : j < H.N),
      F j = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).castSucc))
        ∧ F (j + 1) = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).succ)) := by
    intro j hj
    have hidx0 : (⟨min j H.N, Nat.lt_succ_of_le (min_le_right j H.N)⟩ : Fin (H.N + 1))
        = (⟨j, hj⟩ : Fin H.N).castSucc := by
      apply Fin.ext
      change min j H.N = j
      omega
    have hidx1 : (⟨min (j + 1) H.N, Nat.lt_succ_of_le (min_le_right (j + 1) H.N)⟩
          : Fin (H.N + 1)) = (⟨j, hj⟩ : Fin H.N).succ := by
      apply Fin.ext
      change min (j + 1) H.N = j + 1
      omega
    refine ⟨?_, ?_⟩
    · simp only [hFdef]
      rw [hidx0]
    · simp only [hFdef]
      rw [hidx1]
  have hstep : ∀ j ∈ Finset.range H.N,
      (if h : j < H.N then
        (if a ≤ H.partition (⟨j, h⟩ : Fin H.N).castSucc
            ∧ H.partition (⟨j, h⟩ : Fin H.N).succ ≤ b then C else 0) ^ 2
          * (H.partition (⟨j, h⟩ : Fin H.N).succ - H.partition (⟨j, h⟩ : Fin H.N).castSucc)
        else 0) ≤ C ^ 2 * (F (j + 1) - F j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [dif_pos hj]
    obtain ⟨hFj, hFj1⟩ := hFval j hj
    have hmono := H.partition_strictMono (Fin.castSucc_lt_succ (i := (⟨j, hj⟩ : Fin H.N)))
    by_cases hin : a ≤ H.partition (⟨j, hj⟩ : Fin H.N).castSucc
        ∧ H.partition (⟨j, hj⟩ : Fin H.N).succ ≤ b
    · rw [if_pos hin, hFj, hFj1,
        max_eq_right hin.1, max_eq_right (le_trans hin.1 hmono.le),
        min_eq_right (le_trans hmono.le hin.2), min_eq_right hin.2]
    · rw [if_neg hin]
      have : F j ≤ F (j + 1) := hFmono j
      nlinarith [sq_nonneg C]
  calc H.varClock
        (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0) H.N
      ≤ ∑ j ∈ Finset.range H.N, C ^ 2 * (F (j + 1) - F j) := Finset.sum_le_sum hstep
    _ = C ^ 2 * (F H.N - F 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ C ^ 2 * (b - a) := by
        have hup : F H.N ≤ b := min_le_left _ _
        have hlow : a ≤ F 0 := le_min hab (le_max_left _ _)
        nlinarith [sq_nonneg C]
end LevyStochCalc.Brownian.Ito


