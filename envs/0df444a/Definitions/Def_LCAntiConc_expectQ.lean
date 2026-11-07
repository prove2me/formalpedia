-- Prove2me | Definitions.Def_LCAntiConc_expectQ
-- name    : LCAntiConc_expectQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:57.349714+00:00
-- url     : https://prove2.me/theorems/94661401-ae60-4076-9ed0-394c4f44097e
-- title:
--   The polynomial $\mathbb E\,q(\langle X,v\rangle)$
-- statement:
--   Let $X\in\mathbb R^d$ be a random vector with law $\mu$ and let $q\in\mathbb R[t]$ be a univariate polynomial. Then
--
--   $$\mathbb E\,q(\langle X,v\rangle)\in\mathbb R[v]$$
--
--   is the expectation polynomial of the random polynomial $x\mapsto q(\langle x,v\rangle)$: each coefficient is a moment of $X$. Its value at a vector $u$ is $\mathbb E\,q(\langle X,u\rangle)$.
--
--   This is the polynomial whose sum-of-squares upper bound on the sphere is an anti-concentration certificate (Definition 1.1).
--
--   **Formalization Note** A random vector is represented by its law on `EuclideanSpace ℝ (Fin d)`. The object is a polynomial, not the function $u\mapsto\mathbb E\,q(\langle X,u\rangle)$.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4)

import Mathlib
import Definitions.Def_LCAntiConc_polyExpect
import Definitions.Def_LCAntiConc_linForm

namespace LCAntiConc

open MeasureTheory

/-- The polynomial `𝔼 q(⟨X, v⟩)` in the formal variable `v`, for a random vector `X ∈ ℝ^d` with
law `μ` and a univariate polynomial `q`: the coefficient at each monomial is the expectation of
the corresponding coefficient of `q(⟨x, v⟩)`, a moment of `X`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), (1.3), p.2 (PDF p.4).

**Formalization Note** A random vector is represented by its law `μ` on
`EuclideanSpace ℝ (Fin d)`. The object is a polynomial, not the function `u ↦ ∫ q(⟨x, u⟩) dμ`
(which is its evaluation). -/
noncomputable def expectQ {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (q : Polynomial ℝ) :
    MvPolynomial (Fin d) ℝ :=
  polyExpect μ (fun x => Polynomial.aeval (linForm x) q)

end LCAntiConc


