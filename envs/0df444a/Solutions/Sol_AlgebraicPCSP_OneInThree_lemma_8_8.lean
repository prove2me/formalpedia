-- Prove2me | solution 1 for AlgebraicPCSP.OneInThree.lemma_8_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:45:43.508191+00:00
-- url     : https://prove2.me/submissions/fd7c065c-43ff-4b73-9caa-79f3a09b2ac4

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices
set_option autoImplicit false
open AlgebraicPCSP.OneInThree

lemma ss_val_finRotate (n : ℕ) (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : i = Fin.last n
    · subst h; simp
    · have : i.val + 1 ≠ n + 1 := by
        intro h'; apply h; ext; simpa using h'
      rw [if_neg h, if_neg this]

lemma ss_rot_e (p : ℕ) (hp : 0 < p) (i j : Fin p) :
    finRotate (p * p) (finProdFinEquiv (i, j)) =
      finProdFinEquiv ((if j.val + 1 = p then finRotate p i else i), finRotate p j) := by
  apply Fin.ext
  rw [ss_val_finRotate]
  simp only [finProdFinEquiv_apply_val]
  have hi := i.2
  have hj := j.2
  by_cases hjl : j.val + 1 = p
  · rw [if_pos hjl, ss_val_finRotate p j, if_pos hjl, ss_val_finRotate p i]
    by_cases hil : i.val + 1 = p
    · rw [if_pos hil]
      have : j.val + p * i.val + 1 = p * p := by
        have h2 : p * (i.val + 1) = p * i.val + p := by ring
        have h3 : p * (i.val + 1) = p * p := by rw [hil]
        omega
      rw [if_pos this]; simp
    · rw [if_neg hil]
      have h1 : p * (i.val + 1) < p * p := Nat.mul_lt_mul_of_pos_left (by omega) hp
      have : j.val + p * i.val + 1 ≠ p * p := by
        have : p * (i.val + 1) = p * i.val + p := by ring
        omega
      rw [if_neg this]
      have : p * (i.val + 1) = p * i.val + p := by ring
      omega
  · rw [if_neg hjl, ss_val_finRotate, if_neg hjl]
    have h1 : p * (i.val + 1) ≤ p * p := Nat.mul_le_mul_left p (by omega)
    have h2 : p * (i.val + 1) = p * i.val + p := by ring
    have : j.val + p * i.val + 1 ≠ p * p := by omega
    rw [if_neg this]
    omega

theorem solution {D : Type} {p : ℕ} (s : (Fin p → D) → D) (hcyc : IsCyclic s) :
    IsCyclic (tFlat s) := by
  intro x
  unfold tFlat tOp toMatrix
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : (x ∘ finRotate (0 * 0)) = x := by
      funext k; exact absurd k.2 (by simp)
    rw [this]
  · set c : Fin p → D := fun j => s (fun i => x (finProdFinEquiv (i, j))) with hc
    have key : (fun j => s (fun i => (x ∘ finRotate (p * p)) (finProdFinEquiv (i, j)))) =
        c ∘ finRotate p := by
      funext j
      simp only [Function.comp, hc]
      by_cases hjl : j.val + 1 = p
      · have : ∀ i, x (finRotate (p * p) (finProdFinEquiv (i, j))) =
            (fun i' => x (finProdFinEquiv (i', finRotate p j))) (finRotate p i) := by
          intro i
          rw [ss_rot_e p hp, if_pos hjl]
        simp_rw [this]
        exact (hcyc (fun i' => x (finProdFinEquiv (i', finRotate p j)))).symm
      · have : ∀ i, x (finRotate (p * p) (finProdFinEquiv (i, j))) =
            x (finProdFinEquiv (i, finRotate p j)) := by
          intro i
          rw [ss_rot_e p hp, if_neg hjl]
        simp_rw [this]
    rw [key]
    exact hcyc c
