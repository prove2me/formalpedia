-- Prove2me | Definitions.Def_MonoidProdQ_DualFeasible
-- name    : MonoidProdQ_DualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:16.727935+00:00
-- url     : https://prove2.me/theorems/caa85fc1-ad26-436f-a713-55f1b5ade137
-- title:
--   All-pairs dual (Eq. (3))
-- statement:
--   Let $f$ be a function on a finite promise domain $D\subseteq\Sigma^I$. A family of vectors $u_{x,i},v_{y,i}\in\mathbb C^d$ ($x,y\in D$, $i\in I$) is an **all-pairs dual** for $f$ if
--
--   $$\sum_{i:\,x_i\ne y_i}\langle u_{x,i},v_{y,i}\rangle=1[f(x)\ne f(y)]\qquad\text{for every } x,y\in D.$$
--
--   The condition includes pairs with the same output, for which the sum must be zero.
--
--   **Formalization Note** The paper does not name the field of the vectors; complex vectors are used, which include real ones. The inner product is conjugate-linear in its first argument.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (3), p.25

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eq. (3), p.25: the vectors `u_{x,i}, v_{y,i} ∈ ℂ^d` (`x, y ∈ D`, `i ∈ I`) form
an all-pairs dual for `f` on `D`:
`Σ_{i : xᵢ ≠ yᵢ} ⟨u_{x,i}, v_{y,i}⟩ = 1[f(x) ≠ f(y)]` "for every x, y", including pairs with
the same output, for which the sum must be zero.

**Formalization Note.** The paper does not name the field of the vectors; complex vectors are
used (they include the real ones). `inner ℂ` is conjugate-linear in its first argument. -/
def DualFeasible {I Sig Out : Type*} [Fintype I] [DecidableEq Sig] [DecidableEq Out]
    (f : (I → Sig) → Out) (D : Finset (I → Sig)) {d : ℕ}
    (u v : D → I → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ x y : D,
    ∑ i ∈ Finset.univ.filter (fun i => (x : I → Sig) i ≠ (y : I → Sig) i),
      inner ℂ (u x i) (v y i) = if f x ≠ f y then 1 else 0

end MonoidProdQ


