-- Prove2me | Definitions.Def_PlantedIQP_IsIndependentSpace
-- name    : PlantedIQP_IsIndependentSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:18.359191+00:00
-- url     : https://prove2.me/theorems/b0c0471b-8e2b-4437-8de0-bda5abe2fca5
-- title:
--   Independent spaces of a cubic polynomial (Definition 1)
-- statement:
--   Let $g$ be a cubic polynomial in $n$ variables. A subspace $V\le\mathbb F_2^n$ is an **independent space** of $g$ if there is $A\in GL(n,\mathbb F_2)$ whose first $\dim V$ columns span $V$ and such that $g\circ A$ has an **independent set on the first $\dim V$ coordinates**: the coefficient of $x_ix_jx_k$ in $g\circ A$ vanishes whenever $i<j<k\le\dim V$.
--
--   This is the linear-algebraic analogue of an independent set of a 3-uniform hypergraph, with the symmetric group replaced by $GL(n,\mathbb F_2)$. A planted independent space of dimension $h$ lets the verifier compute amplitudes in time $2^{n-h}\mathrm{poly}(n)$ (Theorem 41).
--
--   **Formalization Note** $\dim V$ is `Module.finrank`; column $j$ of $A$ is the vector $i\mapsto A_{ij}$, and the first $d$ columns are those with index $j<d$ (indices `Fin n`, shifted by one).
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 1, p.5 and proof of Proposition 20, p.16

import Mathlib
import Definitions.Def_PlantedIQP_comp

set_option autoImplicit false

namespace PlantedIQP

/-!
# Independent spaces of a cubic polynomial

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Definition 1, p.5: "Let g : 𝔽₂ⁿ → 𝔽₂ be a cubic
polynomial. We say that V ≤ 𝔽₂ⁿ is an independent space of g, if there exists A ∈ GL(n, 𝔽₂) whose
first dim(V) columns generate V and g ◦ A has an independent set on the first dim(V) coordinates."
An independent set of the 3-uniform hypergraph `H(g)` is a vertex set containing no hyperedge (p.4);
for `H(g ◦ A)` this means: the coefficient of `x_i x_j x_k` in `g ◦ A` vanishes whenever
`i < j < k ≤ dim(V)` (proof of Proposition 20, p.16).

**Formalization Note.**
* `V` is a `Submodule (ZMod 2) (Vec n)` and `dim(V)` its `Module.finrank`.
* Column `j` of `A` is the vector `i ↦ A i j`; "the first `d` columns" are those with `j < d`
  (indices `Fin n`, shifted by one from the source).
* `g ◦ A` is `CubicPoly.comp` (the multilinear representative of `x ↦ g(Ax)`).
-/

/-- The coordinates `{x_1, …, x_d}` (here `Fin n` indices `< d`) are an independent set of the
hypergraph `H(g)`: no monomial `x_i x_j x_k` among them has coefficient `1`. -/
def IndepOnFirst {n : ℕ} (g : CubicPoly n) (d : ℕ) : Prop :=
  ∀ S : Mono n 3, (∀ i ∈ S.1, (i : ℕ) < d) → g.c3 S = 0

/-- `V` is an independent space of `g` (Definition 1): some `A ∈ GL(n, 𝔽₂)` has its first `dim V`
columns spanning `V`, and `g ◦ A` has an independent set on the first `dim V` coordinates. -/
def IsIndependentSpace {n : ℕ} (g : CubicPoly n) (V : Submodule (ZMod 2) (Vec n)) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2),
    Submodule.span (ZMod 2)
        (Set.range fun j : {j : Fin n // (j : ℕ) < Module.finrank (ZMod 2) V} =>
          fun i => (A : Matrix (Fin n) (Fin n) (ZMod 2)) i j) = V ∧
      IndepOnFirst (g.comp A) (Module.finrank (ZMod 2) V)

end PlantedIQP


