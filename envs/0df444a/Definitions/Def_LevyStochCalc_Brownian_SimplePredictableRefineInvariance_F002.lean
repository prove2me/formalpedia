-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F002
-- name    : LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:58:14.833178+00:00
-- url     : https://prove2.me/theorems/19a52d6d-a346-4caf-b28b-76a969d009bb
-- title:
--   Source declarations: LevyStochCalc.Brownian.SimplePredictableRefineInvariance
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.SimplePredictableRefineInvariance. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001

open private sum_Ico_telescope_real from Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F001
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

/-- **Fiber-to-Ico forward direction:** if `j : Fin M` is in the fiber
`{j | idxMap j = i}` and `π' k_lo = H.partition i.castSucc`,
`π' k_hi = H.partition i.succ`, then `j.val ∈ [k_lo.val, k_hi.val)`.
Used by `simpleIntegral_refine` for the bijection between the fiber
and the Ico. -/
lemma SimplePredictable.val_mem_Ico_of_idxMap_eq
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    {i : Fin H.N} {k_lo k_hi : Fin (M + 1)}
    (hk_lo : π' k_lo = H.partition i.castSucc)
    (hk_hi : π' k_hi = H.partition i.succ)
    {j : Fin M} (hj_eq : idxMap j = i) :
    j.val ∈ Finset.Ico k_lo.val k_hi.val := by
  have h_le : H.partition (idxMap j).castSucc ≤ π' j.castSucc := h_idx_le j
  have h_ge : π' j.succ ≤ H.partition (idxMap j).succ := h_idx_ge j
  rw [hj_eq, ← hk_lo] at h_le
  rw [hj_eq, ← hk_hi] at h_ge
  have h_k_lo_le : k_lo.val ≤ j.castSucc.val := h_strictMono.le_iff_le.mp h_le
  have h_succ_le_k_hi : j.succ.val ≤ k_hi.val := h_strictMono.le_iff_le.mp h_ge
  rw [Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  · simpa [Fin.castSucc] using h_k_lo_le
  · have := h_succ_le_k_hi; simp [Fin.succ] at this; omega
/-- **Per-fiber telescope (W-version):** define
`g : ℕ → ℝ := fun n => W (π' ⟨n, h⟩) ω if h : n < M+1 else 0`. Then
`∑ n ∈ Finset.Ico a b, (g (n+1) - g n) = g b - g a` by
`sum_Ico_telescope_real`. The `simpleIntegral_refine` general proof
sets up this `g`, equates the per-fiber Ico-sum to `g (k_hi) - g (k_lo)`,
then matches `g (k_hi) = W (π' k_hi) ω = W (H.partition i.succ) ω` via
`hk_hi`. -/
lemma SimplePredictable.W_telescope_via_g
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {M : ℕ} (π' : Fin (M + 1) → ℝ) (ω : Ω)
    (a b : ℕ) (hab : a ≤ b) (hb_le : b ≤ M) :
    (∑ n ∈ Finset.Ico a b,
      ((fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0) (n + 1)
        - (fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0) n))
      = W.W (π' ⟨b, by omega⟩) ω - W.W (π' ⟨a, by omega⟩) ω := by
  rw [sum_Ico_telescope_real a b hab
    (fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0)]
  have h_b_lt : b < M + 1 := by omega
  have h_a_lt : a < M + 1 := by omega
  simp only [h_b_lt, h_a_lt, dif_pos]
end LevyStochCalc.Brownian.Ito


