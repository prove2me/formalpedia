-- Prove2me | Definitions.Def_TrDegJac_jacobian
-- name    : TrDegJac_jacobian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:15.302431+00:00
-- url     : https://prove2.me/theorems/85149ec4-7bb3-48f6-abd4-69d1757412d7
-- title:
--   The Jacobian matrix $\mathrm{Jac}_x(f)$ over $\mathbb F(x)$
-- statement:
--   Let $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$. The **Jacobian** of $f$ is the $n\times m$ matrix
--   $$
--   \mathrm{Jac}_x(f)_{i,j}=\frac{\partial f_j}{\partial x_i}\qquad(1\le i\le n,\ 1\le j\le m),
--   $$
--   whose rows are indexed by the variables and whose columns are indexed by the polynomials. Its entries lie in $\mathbb F[x]$ and are regarded as elements of $\mathbb F(x)$, so that $\operatorname{rank}_{\mathbb F(x)}\mathrm{Jac}_x(f)$ is the rank over the rational function field.
--
--   The Jacobian rank is the efficiently computable quantity that the mission compares with the transcendence degree.
--
--   **Formalization Note** The entries are `toRatFn (pderiv i (f j))` and the rank is `Matrix.rank` over `FractionRing (MvPolynomial (Fin n) F)`, not over `F[x]` and not at a point. The family may be indexed by any type.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Definition 4.5, p.26

import Mathlib
import Definitions.Def_TrDegJac_RatFn

set_option autoImplicit false

namespace TrDegJac

/-- **The Jacobian matrix over `F(x)`** — Forbes and Staicu, *Approximating Transcendence Degree in
Medium Characteristic*, STOC 2027 submission (manuscript sha256 3ab72a42…), Definition 4.5, p.26:
"the Jacobian of f₁, …, f_m is the n × m matrix Jac_x(f) ∈ F[x]^{n×m} where Jac_x(f)_{i,j} := ∂_{x_i}(f_j)."

Rows are indexed by the variables `x_i`, columns by the polynomials `f_j`.

**Formalization Note.** The entries `∂f_j/∂x_i ∈ F[x]` are mapped into the fraction field
`F(x) = RatFn F n`, so that `Matrix.rank` of `jacobian f` is the paper's `rank_{F(x)} Jac_x(f)`
(rank over the field of rational functions, not over `F[x]` and not at a point). The family may be
indexed by any type `ι`. -/
noncomputable def jacobian {F : Type*} [Field F] {n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) F) : Matrix (Fin n) ι (RatFn F n) :=
  fun i j => toRatFn (MvPolynomial.pderiv i (f j))

end TrDegJac


