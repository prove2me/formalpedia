-- Prove2me | Definitions.Def_ResultantVNP_tensorDet
-- name    : ResultantVNP_tensorDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:29.57618+00:00
-- url     : https://prove2.me/theorems/13e179ea-eff2-43a9-93d7-b89255e64b1f
-- title:
--   Tensor determinant $\mathrm{Det}_n$ of a generic cubic tensor
-- statement:
--   A cubic tensor of dimension $n$ is an array $A=(a_{ijk})_{i,j,k\in[n]}$; for the generic tensor the entries are independent variables. It defines the quadratic map
--
--   $$
--   (Ax^2)_i=\sum_{j,k=1}^n a_{ijk}x_jx_k ,
--   $$
--
--   and its **tensor determinant** is the resultant of these quadratic forms:
--
--   $$
--   \mathrm{Det}_n(A)=\mathrm{Res}^{(2)}_n\big((Ax^2)_1,\dots,(Ax^2)_n\big),
--   $$
--
--   an integral polynomial in the $n^3$ entries $a_{ijk}$. It vanishes exactly when $Ax^2=0$ has a nonzero solution.
--
--   **Formalization Note** The coefficient of $x^e$ in $(Ax^2)_i$ is $a_{ijj}$ for $e=2\mathbf e_j$ and $a_{ijk}+a_{ikj}$ for $e=\mathbf e_j+\mathbf e_k$, $j\ne k$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 2.7, Eq. (1), p.13

import Mathlib
import Definitions.Def_ResultantVNP_quadRes

namespace ResultantVNP

/-- The **quadratic form** `(Ax²)_i = ∑_{j,k=1}^n a_{ijk} x_j x_k` of the generic cubic tensor
`A = (a_{ijk})`, as a polynomial in `x` whose coefficients are polynomials in the entries `a_{ijk}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 2.7, p.13. -/
noncomputable def tensorForm (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) ℤ) :=
  ∑ j : Fin n, ∑ k : Fin n,
    MvPolynomial.C (MvPolynomial.X (i, j, k)) * MvPolynomial.X j * MvPolynomial.X k

/-- The **tensor determinant** `Det_n` of the generic cubic tensor `A = (a_{ijk})_{i,j,k ∈ [n]}` of
dimension `n`: the resultant of the quadratic forms `(Ax²)_i = ∑_{j,k} a_{ijk} x_j x_k`,
`Det_n(A) = Res^{(2)}_n((Ax²)₁, …, (Ax²)ₙ)`, a polynomial with integer coefficients in the `n³`
independent entries `a_{ijk}`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 2.3 and Definition 2.7, Eq. (1), p.13.

**Formalization Note** Each coefficient variable `u_{i,e}` of `Res^{(2)}_n` is replaced by the
coefficient of `x^e` in `(Ax²)_i`: `a_{ijj}` for `e = 2e_j` and `a_{ijk} + a_{ikj}` for `e = e_j + e_k`,
`j ≠ k`. The entries are indexed by `Fin n × Fin n × Fin n` (0-based). The resultant comes from a
`ResultantSystem` (see its note); `Det_n` is meaningful for `n ≥ 1`. -/
noncomputable def tensorDet (𝓡 : ResultantSystem) (n : ℕ) :
    MvPolynomial (Fin n × Fin n × Fin n) ℤ :=
  MvPolynomial.aeval
    (fun v : CoeffVar (fun _ : Fin n => 2) => (tensorForm n v.1).coeff v.2.1) (quadRes 𝓡 n)

end ResultantVNP


