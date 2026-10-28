-- Prove2me | solution 1 for AsyncSA.Monotone.lemma4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:17:57.028804+00:00
-- url     : https://prove2.me/submissions/662798bb-ae65-4440-beae-41bec43af196

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace Aux_AsyncSA_lemma4

theorem avg_between {n : ℕ} (a b : Fin n → ℝ) (h : b ≤ a) :
    b ≤ (1 / 2 : ℝ) • (a + b) ∧ (1 / 2 : ℝ) • (a + b) ≤ a := by
  constructor
  · intro i
    have := h i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linarith
  · intro i
    have := h i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linarith

end Aux_AsyncSA_lemma4

open AsyncSA.Monotone Aux_AsyncSA_lemma4 in
theorem solution {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 F xstar) (hr : 0 < r) (k : ℕ) :
    (F (Useq F xstar r k) ≤ Useq F xstar r (k + 1) ∧
        Useq F xstar r (k + 1) ≤ Useq F xstar r k) ∧
      (Lseq F xstar r (k + 1) ≤ F (Lseq F xstar r k) ∧
        Lseq F xstar r k ≤ Lseq F xstar r (k + 1)) := by
  have hU : ∀ k, F (Useq F xstar r k) ≤ Useq F xstar r k := by
    intro k
    induction k with
    | zero =>
      have := (h4.shift xstar r hr).2.2
      rw [h4.fixed] at this
      exact this
    | succ k ih =>
      have hb := avg_between _ _ ih
      have hmono : F (Useq F xstar r (k + 1)) ≤ F (Useq F xstar r k) := h4.mono hb.2
      exact hmono.trans hb.1
  have hL : ∀ k, Lseq F xstar r k ≤ F (Lseq F xstar r k) := by
    intro k
    induction k with
    | zero =>
      have := (h4.shift xstar r hr).1
      rw [h4.fixed] at this
      exact this
    | succ k ih =>
      have hb := avg_between _ _ ih
      have hmono : F (Lseq F xstar r k) ≤ F (Lseq F xstar r (k + 1)) := by
        apply h4.mono
        show Lseq F xstar r k ≤ (1 / 2 : ℝ) • (Lseq F xstar r k + F (Lseq F xstar r k))
        rw [add_comm]
        exact hb.1
      refine le_trans ?_ hmono
      show (1 / 2 : ℝ) • (Lseq F xstar r k + F (Lseq F xstar r k)) ≤ F (Lseq F xstar r k)
      rw [add_comm]
      exact hb.2
  have hb := avg_between _ _ (hU k)
  have hb' := avg_between _ _ (hL k)
  refine ⟨⟨hb.1, hb.2⟩, ⟨?_, ?_⟩⟩
  · show (1 / 2 : ℝ) • (Lseq F xstar r k + F (Lseq F xstar r k)) ≤ F (Lseq F xstar r k)
    rw [add_comm]
    exact hb'.2
  · show Lseq F xstar r k ≤ (1 / 2 : ℝ) • (Lseq F xstar r k + F (Lseq F xstar r k))
    rw [add_comm]
    exact hb'.1
