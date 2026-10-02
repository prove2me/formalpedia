-- Prove2me | Definitions.Def_LeblSCV_Levi_holTangent
-- name    : LeblSCV_Levi_holTangent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:33:12.627988+00:00
-- url     : https://prove2.me/theorems/39b56c3b-ec51-4bd9-8c57-4f74ff35eb80
-- title:
--   Holomorphic tangent space $T^{(1,0)}_p \partial U$ from a defining function
-- statement:
--   Let $r$ be a real defining function of a real hypersurface $M \subset \mathbb{C}^n$ at $p \in M$. The space of **holomorphic tangent vectors** is $T^{(1,0)}_p M = (\mathbb{C}T_pM) \cap T^{(1,0)}_p\mathbb{C}^n$; a vector $X_p = \sum_k a_k \frac{\partial}{\partial z_k}\big|_p$ lies in it exactly when $X_p r = 0$, that is,
--   $$T^{(1,0)}_p M = \Big\{ a \in \mathbb{C}^n : \sum_{k=1}^n a_k \left.\frac{\partial r}{\partial z_k}\right|_p = 0 \Big\}.$$
--   It is a complex subspace of dimension $n - 1$ (Proposition 2.3.3).
--
--   **Formalization Note.** `holTangent r p` is this set as a `Submodule ℂ (Fin n → ℂ)` of coefficient vectors.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 64 (ℂT_pM and T_p^{(1,0)}M)

import Mathlib
import Definitions.Def_LeblSCV_Levi_wirtingerZ

namespace LeblSCV.Levi

/-- `T_p^{(1,0)} ∂U = ℂT_p ∂U ∩ T_p^{(1,0)} ℂⁿ` (Lebl, p. 64), computed from a defining function
`r`: the coefficient vectors `a` of `X_p = ∑ a_k ∂/∂z_k|_p` with `X_p r = ∑ a_k ∂r/∂z_k(p) = 0`. -/
noncomputable def holTangent {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {a | ∑ k, a k * wirtingerZ (fun z => (r z : ℂ)) k p = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_assoc] at *
    rw [← Finset.mul_sum, ha, mul_zero]

end LeblSCV.Levi


