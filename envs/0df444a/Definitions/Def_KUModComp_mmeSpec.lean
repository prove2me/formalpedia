-- Prove2me | Definitions.Def_KUModComp_mmeSpec
-- name    : KUModComp_mmeSpec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:30.097059+00:00
-- url     : https://prove2.me/theorems/ed530ae0-1f38-466f-af7f-6c0d1950b23f
-- title:
--   Dense multivariate polynomials and MULTIVARIATE MULTIPOINT EVALUATION
-- statement:
--   Let $R$ be a commutative ring and $d, m, N \in \mathbb N$.
--
--   1. A polynomial $f \in R[X_0,\dots,X_{m-1}]$ with **individual degrees at most $d-1$** is given densely, by one coefficient $c_e \in R$ for every exponent vector $e = (e_0,\dots,e_{m-1}) \in \{0,\dots,d-1\}^m$:
--   $$
--   f = \sum_{e \in \{0,\dots,d-1\}^m} c_e \, X_0^{e_0} \cdots X_{m-1}^{e_{m-1}} .
--   $$
--   2. **MULTIVARIATE MULTIPOINT EVALUATION** with parameters $d, m, N$ (Problem 2.1): given such an $f$ and evaluation points $\alpha_0,\dots,\alpha_{N-1} \in R^m$, output the $N$ values
--   $$
--   f(\alpha_k) = \sum_{e} c_e \prod_{i<m} \alpha_{k,i}^{\,e_i}, \qquad k = 0,\dots,N-1 .
--   $$
--
--   This is the oracle problem to which MODULAR COMPOSITION is reduced in Theorem 3.1, and the input format of the oracle instruction of the straight-line-program model.
--
--   **Formalization Note** Exponent vectors are functions `Fin m → Fin d`, so "individual degrees at most $d-1$" is built into the type. `densePolyMv` is the polynomial $f$ as an `MvPolynomial`; `mmeSpec` is the list of values.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Problem 2.1, p. 7; dense representation, §2.2, p. 8 ("polynomials are always represented explicitly by a list of their coefficients")

import Mathlib

open MvPolynomial

namespace KUModComp

variable {R : Type*} [CommRing R]

/-- **Dense multivariate polynomial.** Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008),
§2, p. 8: "polynomials are always represented explicitly by a list of their coefficients".
A polynomial in `X_0, …, X_{m-1}` with individual degrees at most `d - 1` is given by its
coefficients `c e`, one for each exponent vector `e : Fin m → Fin d`; this is the polynomial
`∑_e c e · X_0^{e 0} ⋯ X_{m-1}^{e (m-1)}`. -/
noncomputable def densePolyMv {d m : ℕ} (c : (Fin m → Fin d) → R) : MvPolynomial (Fin m) R :=
  ∑ e : Fin m → Fin d, monomial (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) (c e)

/-- **MULTIVARIATE MULTIPOINT EVALUATION** (Problem 2.1, p. 7). Given the coefficients
`c : (Fin m → Fin d) → R` of `f(X_0, …, X_{m-1})` with individual degrees at most `d - 1` and
evaluation points `α 0, …, α (N-1)` in `R^m`, the output is `f(α k)` for `k = 0, …, N - 1`:
`mmeSpec c α k = ∑_e c e · ∏_i (α k i)^{e i}`. -/
def mmeSpec {d m N : ℕ} (c : (Fin m → Fin d) → R) (α : Fin N → Fin m → R) : Fin N → R :=
  fun k => ∑ e : Fin m → Fin d, c e * ∏ i, α k i ^ (e i : ℕ)

end KUModComp


