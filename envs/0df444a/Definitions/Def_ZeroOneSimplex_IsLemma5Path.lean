-- Prove2me | Definitions.Def_ZeroOneSimplex_IsLemma5Path
-- name    : ZeroOneSimplex_IsLemma5Path
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:36.96934+00:00
-- url     : https://prove2.me/theorems/15552b6f-15e8-47d0-b9b8-89f850bc334d
-- title:
--   The $f$-minimal improving neighbors and the path of Lemma 5
-- statement:
--   Fix a starting vertex $x^0$ of $Q$ and the index function $f$. For a vertex $x$, $N_{\min}(x)$ is the set of $c$-improving neighbors of $x$ with the least value of $f$.
--
--   A **Lemma 5 path** starts at $x^0$ and moves from $x^i$ to a $c$-maximum $x^{i+1}$ of $N_{\min}(x^i)$ (any one when there are several).
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, Lemma 5, p.17

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec

set_option autoImplicit false

namespace ZeroOneSimplex

/-- `N_min(x)` (arXiv:2111.14050v1, Lemma 5, p.17): the **`f`-minimal `c`-improving neighbors**
of `x` in `Q`, where `f = fIndex x⁰`. -/
def minImprovingNbrs {n : ℕ} (Q : Set (Fin n → ℝ)) (c x0 x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | u ∈ improvingNbrs Q c x ∧ ∀ u' ∈ improvingNbrs Q c x, fIndex x0 u ≤ fIndex x0 u'}

/-- **The path of Lemma 5** (arXiv:2111.14050v1, p.17): it starts at the vertex `x⁰`, and from
`x i` it moves to a `c`-maximum of `N_min(x i)` (any one, if several). `x 0, …, x k` is a finite
initial part of such a path. -/
def IsLemma5Path {n : ℕ} (Q : Set (Fin n → ℝ)) (c x0 : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (k : ℕ) : Prop :=
  x 0 = x0 ∧ x0 ∈ Set.extremePoints ℝ Q ∧
    ∀ i < k, x (i + 1) ∈ minImprovingNbrs Q c x0 (x i) ∧
      ∀ u ∈ minImprovingNbrs Q c x0 (x i), c ⬝ᵥ u ≤ c ⬝ᵥ x (i + 1)

end ZeroOneSimplex


