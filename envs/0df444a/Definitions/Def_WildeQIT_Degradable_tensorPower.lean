-- Prove2me | Definitions.Def_WildeQIT_Degradable_tensorPower
-- name    : WildeQIT_Degradable_tensorPower
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:26.264985+00:00
-- url     : https://prove2.me/theorems/7df7019c-3d5e-440e-825d-558ad994cc2b
-- title:
--   Tensor-power channel $\mathcal N^{\otimes n}$
-- statement:
--   For a quantum channel $\mathcal N$ with Kraus operators $\{K_i\}$ and $n\in\mathbb N$, the **tensor-power channel** $\mathcal N^{\otimes n}$ describes $n$ independent uses of $\mathcal N$ on the inputs $A_1'\cdots A_n'$; its Kraus operators are
--
--   $$
--   K_{i_1}\otimes\cdots\otimes K_{i_n},
--   $$
--
--   indexed by strings $(i_1,\dots,i_n)$. It appears in the regularized quantities $\lim_n \frac1n I(\mathcal N^{\otimes n})$, $\lim_n\frac1n Q(\mathcal N^{\otimes n})$ and $P_{\mathrm{reg}}(\mathcal N)=\lim_n\frac1nP(\mathcal N^{\otimes n})$ (13.182).
--
--   **Formalization Note** The $n$-fold system is the function type `Fin n → a`; a Kraus operator has entries $\prod_k K_{i_k}(y_k,x_k)$. At $n=0$ the system is one-dimensional and the channel is the identity.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.1, eqs. (13.9)–(13.10), p. 390, and eq. (13.182), p. 416

import Definitions.Def_WildeQIT_QChannel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Pi

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.1 (13.9)–(13.10), p. 390, and (13.182), p. 416
(the tensor-power channel `N^{⊗n}` of a regularized information quantity).
-/

open Matrix

namespace WildeQIT.Degradable

/-- **Tensor-power channel `N^{⊗n}`** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.1, p. 390, after (13.10),
and (13.182), p. 416): `n` independent uses of the channel `N`, acting on `n` input systems
`A′₁ ⋯ A′ₙ`. If `N` has Kraus operators `K_i`, then `N^{⊗n}` has the Kraus operators
`K_{i₁} ⊗ ⋯ ⊗ K_{iₙ}`, indexed by strings `(i₁, …, iₙ)`.

**Formalization Note.** The `n`-fold system is the function type `Fin n → a` (a string of `n`
input letters), and a Kraus operator `K_f` has the entries `∏ₖ K_{f k}(y k, x k)`. At `n = 0`
the system is one-dimensional and `N^{⊗0}` is the identity channel on it; only `n → ∞`
matters for the regularized quantities. -/
def tensorPower {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) (n : ℕ) :
    QChannel (Fin n → a) (Fin n → b) where
  ι := Fin n → N.ι
  K f := Matrix.of fun y x => ∏ k, N.K (f k) (y k) (x k)
  complete := by
    ext x x'
    have h : ∀ k, ∑ iy : N.ι × b, star (N.K iy.1 iy.2 (x k)) * N.K iy.1 iy.2 (x' k)
        = (1 : Matrix a a ℂ) (x k) (x' k) := by
      intro k
      rw [← N.complete, Fintype.sum_prod_type, Matrix.sum_apply]
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hone : (1 : Matrix (Fin n → a) (Fin n → a) ℂ) x x' =
        ∏ k, (1 : Matrix a a ℂ) (x k) (x' k) := by
      by_cases hx : x = x'
      · subst hx; simp
      · obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
        rw [Matrix.one_apply_ne hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ k)
          (show (1 : Matrix a a ℂ) (x k) (x' k) = 0 from Matrix.one_apply_ne hk)).symm
    rw [hone]
    simp_rw [← h]
    rw [Finset.prod_univ_sum, Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]
    rw [Fintype.piFinset_univ, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ ?_
    intro cj
    simp [Finset.prod_mul_distrib, Equiv.arrowProdEquivProdArrow]

end WildeQIT.Degradable


