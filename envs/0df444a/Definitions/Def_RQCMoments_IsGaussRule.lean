-- Prove2me | Definitions.Def_RQCMoments_IsGaussRule
-- name    : RQCMoments_IsGaussRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:09.356733+00:00
-- url     : https://prove2.me/theorems/3016e793-25ce-4593-9062-6fb28961bfba
-- title:
--   $\ell$-node Gauss quadrature rule (exact to degree $2\ell-1$)
-- statement:
--   Let $\nu$ be a measure on $\mathbb R$ and $\ell\ge 1$. Nodes $x_1<\dots<x_\ell$ and real weights $w_1,\dots,w_\ell$ form an **$\ell$-node Gauss quadrature rule** for $\nu$ if
--   $$
--   \int g\,d\nu=\sum_{i=1}^{\ell} w_i\,g(x_i)\qquad\text{for every real polynomial } g \text{ with } \deg g\le 2\ell-1 .
--   $$
--
--   An $\ell$-node rule with distinct nodes exact up to degree $2\ell-1$ is unique: its nodes are the zeros of the orthonormal polynomial $q_\ell$ and its weights are $w_i=\int \ell_i\,d\nu$ with $\ell_i$ the Lagrange basis polynomials (§4.1). Lemma 4.1 identifies the weights with the Christoffel function, and Theorem 4.4 bounds them for $\mathrm{Beta}(1,D)$.
--
--   **Formalization Note** Exactness includes $\nu$-integrability of each such $g$, so that a non-integrable polynomial cannot count as having integral $0$.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §4.1, (50)–(51); Lemma 4.1; Theorem 4.4, pp.21–22, 25 (PDF pp.23–24, 27)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- An `ℓ`-node Gauss quadrature rule for `ν` (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §4.1, (50)–(51), p.21; Lemma 4.1, p.22;
Theorem 4.4, p.25): strictly increasing nodes `x₁ < ⋯ < x_ℓ` and real weights `w₁, …, w_ℓ`
such that `∫ g dν = ∑ᵢ wᵢ g(xᵢ)` for every real polynomial `g` of degree at most `2ℓ − 1`.

**Formalization Note** Exactness includes `ν`-integrability of each such `g` (otherwise Lean's
Bochner integral would be the junk value `0`). An `ℓ`-node rule with distinct nodes that is
exact up to degree `2ℓ − 1` is unique (its nodes are the zeros of the orthonormal polynomial
`q_ℓ` and its weights are `∫ ℓᵢ dν`), so for a measure as in §2.4 this predicate singles out the
paper's Gauss rule. -/
def IsGaussRule (ν : Measure ℝ) (ℓ : ℕ) (x w : Fin ℓ → ℝ) : Prop :=
  StrictMono x ∧
    ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * ℓ - 1 →
      Integrable (fun t => g.eval t) ν ∧ ∫ t, g.eval t ∂ν = ∑ i, w i * g.eval (x i)

end RQCMoments


