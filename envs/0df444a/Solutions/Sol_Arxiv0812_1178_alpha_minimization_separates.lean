-- Prove2me | solution 1 for Arxiv0812_1178.alpha_minimization_separates
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:37:27.91466+00:00
-- url     : https://prove2.me/submissions/e295f1e3-c367-4b93-8c5a-39023e540549

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
namespace Arxiv0812_1178

theorem alpha_minimization_separates {n : ℕ} (hn : 3 ≤ n) {T P : Type*} [Fintype T] [Fintype P]
    (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (hR : ∀ t, (R t).PosDef) (x : P → ℝ) (α : T → Fin (n - 1) → ℝ) :
    (∀ α' : T → Fin (n - 1) → ℝ,
        myopicCrit H ydata ybar R x α ≤ myopicCrit H ydata ybar R x α') ↔
      ∀ (t : T) (a : Fin (n - 1) → ℝ),
        chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x (α t)) ≤
          chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x a) := by
  classical
  constructor
  · intro h t a
    have h1 := h (Function.update α t a)
    unfold myopicCrit at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ t)] at h1
    have e : ∑ s ∈ Finset.univ.erase t,
        chi2 (ydata s) (ybar s) (R s) (myopicModel (H s) x (Function.update α t a s)) =
        ∑ s ∈ Finset.univ.erase t,
        chi2 (ydata s) (ybar s) (R s) (myopicModel (H s) x (α s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
    rw [e, Function.update_self] at h1
    linarith
  · intro h α'
    unfold myopicCrit
    exact Finset.sum_le_sum (fun t _ => h t (α' t))

end Arxiv0812_1178

open Arxiv0812_1178 in
theorem solution {n : ℕ} (hn : 3 ≤ n) {T P : Type*} [Fintype T] [Fintype P]
    (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (hR : ∀ t, (R t).PosDef) (x : P → ℝ) (α : T → Fin (n - 1) → ℝ) :
    (∀ α' : T → Fin (n - 1) → ℝ,
        myopicCrit H ydata ybar R x α ≤ myopicCrit H ydata ybar R x α') ↔
      ∀ (t : T) (a : Fin (n - 1) → ℝ),
        chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x (α t)) ≤
          chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x a) :=
  Arxiv0812_1178.alpha_minimization_separates hn H ydata ybar R hR x α
