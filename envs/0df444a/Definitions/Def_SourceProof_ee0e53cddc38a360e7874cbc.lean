-- Prove2me | Definitions.Def_SourceProof_ee0e53cddc38a360e7874cbc
-- name    : SourceProof_ee0e53cddc38a360e7874cbc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:10:32.461204+00:00
-- url     : https://prove2.me/theorems/827f51f6-3d55-4c43-923a-28e145a2ba71
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Brownian.Ito.SimplePredictable.fiber_sum_telescope
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F002
import Definitions.Def_SourceProof_ea2e15e39b044c95546402b4

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


theorem _root_.Prove2MeSourceProof.h_ee0e53cddc38a360e7874cbc
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (i : Fin H.N) (ω : Ω) :
    (∑ j ∈ (Finset.univ : Finset (Fin M)).filter (fun j => idxMap j = i),
        H.ξ (idxMap j) ω * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
      = H.ξ i ω
          * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) := by
  obtain ⟨k_lo, hk_lo⟩ := h_refines i.castSucc
  obtain ⟨k_hi, hk_hi⟩ := h_refines i.succ
  have hk_lo_lt_hi : k_lo.val < k_hi.val := by
    have h1 : π' k_lo < π' k_hi := by
      rw [hk_lo, hk_hi]; exact H.partition_strictMono Fin.castSucc_lt_succ
    exact h_strictMono.lt_iff_lt.mp h1
  have hk_hi_le_M : k_hi.val ≤ M := Nat.lt_succ_iff.mp k_hi.isLt
  -- Define the W-valued g function for telescoping.
  set g : ℕ → ℝ := fun n => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0 with hg_def
  -- Convert the fiber sum to an Ico sum via Finset.sum_bij.
  -- Target: ∑ n ∈ Ico k_lo.val k_hi.val, H.ξ i ω · (g (n+1) - g n).
  have h_bij_eq : (∑ j ∈ (Finset.univ : Finset (Fin M)).filter
      (fun j => idxMap j = i),
      H.ξ (idxMap j) ω * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
      = ∑ n ∈ Finset.Ico k_lo.val k_hi.val, H.ξ i ω * (g (n + 1) - g n) := by
    refine Finset.sum_bij
      (i := fun (j : Fin M) (_ : j ∈ (Finset.univ : Finset (Fin M)).filter
        (fun j => idxMap j = i)) => j.val)
      (fun j hj => H.val_mem_Ico_of_idxMap_eq h_strictMono h_idx_le h_idx_ge
        hk_lo hk_hi (Finset.mem_filter.mp hj).2)
      (fun j₁ _ j₂ _ h => Fin.ext h)
      (fun n hn => by
        rw [Finset.mem_Ico] at hn
        have h_lt : n < M := lt_of_lt_of_le hn.2 hk_hi_le_M
        refine ⟨⟨n, h_lt⟩, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        exact (_root_.Prove2MeSourceProof.h_ea2e15e39b044c95546402b4 H) h_strictMono h_idx_le h_idx_ge hk_lo hk_hi
          h_lt hn.1 hn.2)
      ?_
    intro j hj
    have hj_eq : idxMap j = i := (Finset.mem_filter.mp hj).2
    have h_lt_jval : j.val < M := j.isLt
    have h_succ_lt : j.val + 1 < M + 1 := by omega
    have h_lt_M1 : j.val < M + 1 := by omega
    have h_succ_eq : j.succ = (⟨j.val + 1, h_succ_lt⟩ : Fin (M + 1)) :=
      Fin.ext (by simp [Fin.succ])
    have h_castSucc_eq : j.castSucc = (⟨j.val, h_lt_M1⟩ : Fin (M + 1)) :=
      Fin.ext (by simp [Fin.castSucc])
    rw [hj_eq, h_succ_eq, h_castSucc_eq]
    -- Goal: H.ξ i ω · (W (π' ⟨j.val + 1, _⟩) ω - W (π' ⟨j.val, _⟩) ω)
    --     = H.ξ i ω · (g (j.val + 1) - g j.val)
    change H.ξ i ω * (W.W (π' ⟨j.val + 1, h_succ_lt⟩) ω
        - W.W (π' ⟨j.val, h_lt_M1⟩) ω)
      = H.ξ i ω * (g (j.val + 1) - g j.val)
    have hg_succ : g (j.val + 1) = W.W (π' ⟨j.val + 1, h_succ_lt⟩) ω := by
      rw [hg_def]; exact dif_pos h_succ_lt
    have hg_val : g j.val = W.W (π' ⟨j.val, h_lt_M1⟩) ω := by
      rw [hg_def]; exact dif_pos h_lt_M1
    rw [hg_succ, hg_val]
  rw [h_bij_eq]
  -- Now: ∑ n ∈ Ico, H.ξ i ω · (g (n+1) - g n)
  -- = H.ξ i ω · ∑ (g (n+1) - g n)
  -- = H.ξ i ω · (W (π' ⟨k_hi.val, _⟩) ω - W (π' ⟨k_lo.val, _⟩) ω)
  --   [W_telescope_via_g]
  -- = H.ξ i ω · (W (H.partition i.succ) ω - W (H.partition i.castSucc) ω)  [hk_hi, hk_lo]
  rw [← Finset.mul_sum]
  rw [LevyStochCalc.Brownian.Ito.SimplePredictable.W_telescope_via_g (Ω := Ω) (P := P) W π' ω k_lo.val k_hi.val
    (le_of_lt hk_lo_lt_hi) hk_hi_le_M]
  congr 2
  · rw [show (⟨k_hi.val, by omega⟩ : Fin (M + 1)) = k_hi from Fin.ext rfl, hk_hi]
  · rw [show (⟨k_lo.val, by omega⟩ : Fin (M + 1)) = k_lo from Fin.ext rfl, hk_lo]
end LevyStochCalc.Brownian.Ito


