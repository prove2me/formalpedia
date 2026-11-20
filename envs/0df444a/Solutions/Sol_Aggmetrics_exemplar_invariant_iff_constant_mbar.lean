-- Prove2me | solution 1 for Aggmetrics.exemplar_invariant_iff_constant_mbar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:52:50.693403+00:00
-- url     : https://prove2.me/submissions/9e4d2144-56b7-42fe-b5f3-8661e2d4fa64

import Mathlib
import Definitions.Def_Aggmetrics_Basic

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution {k : ℕ} (hk : 0 < k) (mbar : Fin k → ℝ) :
    (∀ share1 share2 : Fin k → ℝ,
      (∀ τ, 0 ≤ share1 τ) → (∑ τ, share1 τ = 1) →
      (∀ τ, 0 ≤ share2 τ) → (∑ τ, share2 τ = 1) →
      ∑ τ, share1 τ * mbar τ = ∑ τ, share2 τ * mbar τ)
    ↔ (∀ τ1 τ2, mbar τ1 = mbar τ2) := by
  constructor
  · intro h τ1 τ2
    have h1 := h (fun τ => if τ = τ1 then 1 else 0) (fun τ => if τ = τ2 then 1 else 0)
      (fun τ => by split <;> norm_num) (by simp)
      (fun τ => by split <;> norm_num) (by simp)
    simp only [mem_univ, ite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq' univ] at h1
    convert h1 using 2
  · intro hconst share1 share2 hs1p hs1 hs2p hs2
    have e1 : ∀ τ, share1 τ * mbar τ = share1 τ * mbar ⟨0, hk⟩ := fun τ => by
      rw [hconst τ ⟨0, hk⟩]
    have e2 : ∀ τ, share2 τ * mbar τ = share2 τ * mbar ⟨0, hk⟩ := fun τ => by
      rw [hconst τ ⟨0, hk⟩]
    rw [Finset.sum_congr rfl (fun τ _ => e1 τ), Finset.sum_congr rfl (fun τ _ => e2 τ),
        ← Finset.sum_mul, ← Finset.sum_mul, hs1, hs2]
end Aggmetrics
