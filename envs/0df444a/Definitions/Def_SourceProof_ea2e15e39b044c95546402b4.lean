-- Prove2me | Definitions.Def_SourceProof_ea2e15e39b044c95546402b4
-- name    : SourceProof_ea2e15e39b044c95546402b4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:07:57.713184+00:00
-- url     : https://prove2.me/theorems/938863b2-d936-42c7-a3d8-4fbe4baa8354
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.SimplePredictable.idxMap_of_mem_Ico
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_ea2e15e39b044c95546402b4
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    {i : Fin H.N} {k_lo k_hi : Fin (M + 1)}
    (hk_lo : π' k_lo = H.partition i.castSucc)
    (hk_hi : π' k_hi = H.partition i.succ)
    {n : ℕ} (h_lt : n < M) (hn_lo : k_lo.val ≤ n) (hn_hi : n < k_hi.val) :
    idxMap ⟨n, h_lt⟩ = i := by
  let j : Fin M := ⟨n, h_lt⟩
  have h_le : H.partition i.castSucc ≤ π' j.castSucc := by
    rw [← hk_lo]
    apply h_strictMono.monotone
    rw [Fin.le_iff_val_le_val]
    show k_lo.val ≤ j.castSucc.val
    have : j.castSucc.val = n := by simp [Fin.castSucc, j]
    rw [this]; exact hn_lo
  have h_ge : π' j.succ ≤ H.partition i.succ := by
    rw [← hk_hi]
    apply h_strictMono.monotone
    rw [Fin.le_iff_val_le_val]
    show j.succ.val ≤ k_hi.val
    have : j.succ.val = n + 1 := by simp [Fin.succ, j]
    rw [this]; omega
  have h_idxMap_le : H.partition (idxMap j).castSucc ≤ π' j.castSucc := h_idx_le j
  have h_idxMap_ge : π' j.succ ≤ H.partition (idxMap j).succ := h_idx_ge j
  by_contra h_ne
  have h_lt_succ : π' j.castSucc < π' j.succ := h_strictMono Fin.castSucc_lt_succ
  let s_test : ℝ := (π' j.castSucc + π' j.succ) / 2
  have h_test_lo : π' j.castSucc < s_test := by
    change π' j.castSucc < (π' j.castSucc + π' j.succ) / 2; linarith
  have h_test_hi : s_test < π' j.succ := by
    change (π' j.castSucc + π' j.succ) / 2 < π' j.succ; linarith
  have h_in_i : s_test ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ) :=
    ⟨lt_of_le_of_lt h_le h_test_lo, le_trans h_test_hi.le h_ge⟩
  have h_in_idx : s_test ∈ Set.Ioc (H.partition (idxMap j).castSucc)
      (H.partition (idxMap j).succ) :=
    ⟨lt_of_le_of_lt h_idxMap_le h_test_lo, le_trans h_test_hi.le h_idxMap_ge⟩
  exact Set.disjoint_iff.mp (H.partition_Ioc_disjoint_of_ne (Ne.symm h_ne)) ⟨h_in_i, h_in_idx⟩
end LevyStochCalc.Brownian.Ito


