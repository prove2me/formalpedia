-- Prove2me | solution 1 for AsyncSA.Monotone.lemma6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:44:24.933521+00:00
-- url     : https://prove2.me/submissions/cfaaabc4-872d-4555-bbf0-bbb8916ef921

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

open AsyncSA.Monotone


theorem solution {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 alg.F xstar) (hr : 0 < r) (ω : Ω) (k tk t'k : ℕ)
    (h18 : ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k)
    (hτ : ∀ t, t'k ≤ t → ∀ i j, tk ≤ alg.τ i j t ω)
    (X : Fin n → ℕ → ℝ)
    (hX0 : ∀ i, X i t'k = Useq alg.F xstar r k i)
    (hX : ∀ i t, t'k ≤ t →
      X i (t + 1) = (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F (Useq alg.F xstar r k) i) :
    ∀ i, ∀ t, t'k ≤ t →
      alg.x t ω i ≤ X i t + tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t := by
  intro i t ht
  have htk : tk ≤ t'k := le_trans (hτ t'k le_rfl i i) (alg.τ_le i i t'k ω)
  induction t, ht using Nat.le_induction with
  | base =>
    have h0 : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t'k = 0 := by
      cases t'k with
      | zero => rfl
      | succ s => simp [tailW]
    rw [h0, hX0, add_zero]
    exact (h18 t'k htk).2 i
  | succ t ht ih =>
    have hupd := alg.update i t ω
    have hα := alg.α_mem i t ω
    have hxi : (fun j => alg.x (alg.τ i j t ω) ω j) ≤ Useq alg.F xstar r k := by
      intro j
      exact (h18 _ (hτ t ht i j)).2 j
    have hF := h4.mono hxi i
    have htail : tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k (t + 1)
        = (1 - alg.α i t ω) * tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t
          + alg.α i t ω * alg.w i t ω := by
      simp only [tailW, if_pos ht]
    rw [hupd, hX i t ht, htail]
    have h1 : 0 ≤ 1 - alg.α i t ω := by linarith [hα.2]
    nlinarith [mul_le_mul_of_nonneg_left ih h1, mul_le_mul_of_nonneg_left hF hα.1]
