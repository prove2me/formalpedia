-- Prove2me | Definitions.Def_RLCDiscrepancy_dual
-- name    : RLCDiscrepancy_dual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:29.842602+00:00
-- url     : https://prove2.me/theorems/3714dcdd-47ef-41b5-b03a-c4882683a7d3
-- title:
--   Dual code $C^\perp$
-- statement:
--   For a linear code $C\subseteq\mathbb F_q^n$, its **dual code** is
--
--   $$
--   C^\perp=\{y\in\mathbb F_q^n : \langle x,y\rangle=0 \text{ for all } x\in C\},\qquad \langle x,y\rangle=\sum_{j=1}^n x_jy_j .
--   $$
--
--   It is the index set of the Fourier expansion of $\delta_{C,f}$ in Eq. (8).
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.12; §4.2, p.30

import Mathlib

namespace RLCDiscrepancy

/-- **Dual code C^⊥** = {y ∈ F^n_q : ⟨x, y⟩ = 0 for all x ∈ C}, with the standard inner product
⟨x, y⟩ = ∑_j x_j y_j of Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.12 (used in §4.2, p.30). -/
def dual {F : Type*} [Field F] [Fintype F] {n : ℕ} (C : Submodule F (Fin n → F)) : Submodule F (Fin n → F) where
  carrier := {y | ∀ x ∈ C, x ⬝ᵥ y = 0}
  add_mem' {a b} ha hb x hx := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [dotProduct_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := dotProduct_zero x
  smul_mem' c y hy x hx := by
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [dotProduct_smul, hy x hx, smul_zero]

end RLCDiscrepancy


