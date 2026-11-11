-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_Normalization
-- name    : SparseLowFactors_BoundedDeg_Normalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:22:46.677092+00:00
-- url     : https://prove2.me/theorems/b58cb9f0-78b3-4f0e-a79e-112c40d4264f
-- title:
--   Normalization and reverse normalization of a polynomial in $Y$
-- statement:
--   Let $A=F[X]$ and $f(X,Y)=\sum_{i=0}^{d} f_i(X)Y^i\in A[Y]$ with $f_d\neq0$ (so $d=\deg_Y f$).
--
--   1. The **normalization** of $f$ is the monic polynomial
--   $$\hat f(X,Y)=f\!\left(X,\frac{Y}{f_d}\right)f_d^{\,d-1}=Y^d+\sum_{i=0}^{d-1} f_i\,f_d^{\,d-1-i}\,Y^i .$$
--   2. If $f_0\neq0$, the **reverse normalization** of $f$ is the reversed-monic polynomial
--   $$\tilde f(X,Y)=\frac{f(X,Yf_0)}{f_0}=1+\sum_{i=1}^{d} f_i\,f_0^{\,i-1}\,Y^i .$$
--
--   The normalization turns a factor of $f$ into a monic factor of $\hat f$ (Lemma 2.23), which is what makes the power-series factoring of Section 3 applicable; the reverse normalization does the same with the constant term (Lemma 2.24).
--
--   **Formalization Note** Both are defined by the coefficient formulas on the right, which are the rational-function expressions on the left written out (the paper's own expansions in the proofs of Lemmas 2.23, 2.24). For $f=0$ the formula gives $1$; the source requires $f_d\ne0$ (resp. $f_0\ne0$) and every statement assumes it. The ring of coefficients is arbitrary; $A=F[X]$ in the mission.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 16, §2.1

import Mathlib

set_option autoImplicit false

/-!
# Normalization and reverse normalization in a main variable `Y`

Bhattacharjee, Kothary, Rai, Saraf, arXiv:2606.27293 (held version, sha256 9837a932…), §2.1, p. 16.
A polynomial `f(X, Y) ∈ F[X, Y]` is a `Polynomial (MvPolynomial σ F)`: `f = Σ_i f_i(X) Y^i`.
-/

namespace SparseLowFactors.BoundedDeg

open Polynomial

variable {R : Type*} [CommRing R]

/-- The normalization (p. 16) `f̂(X, Y) = f(X, Y / f_d) · f_d^{d-1}` of `f = Σ_{i ≤ d} f_i Y^i`
with `d = deg_Y f`, `f_d ≠ 0`. It is the polynomial `Y^d + Σ_{i < d} f_i f_d^{d-1-i} Y^i`: the
coefficient of `Y^d` is `f_d · f_d^{-d} · f_d^{d-1}·f_d = 1`, and of `Y^i`, `i < d`, is
`f_i f_d^{-i} f_d^{d-1}`. -/
noncomputable def normalize (f : Polynomial R) : Polynomial R :=
  X ^ f.natDegree +
    ∑ i ∈ Finset.range f.natDegree, C (f.coeff i * f.leadingCoeff ^ (f.natDegree - 1 - i)) * X ^ i

/-- The reverse normalization (p. 16) `f̃(X, Y) = f(X, Y f_0) / f_0` of `f = Σ_{i ≤ d} f_i Y^i`
with `f_0 ≠ 0`. It is the polynomial `1 + Σ_{1 ≤ i ≤ d} f_i f_0^{i-1} Y^i`. -/
noncomputable def revNormalize (f : Polynomial R) : Polynomial R :=
  1 + ∑ i ∈ Finset.range f.natDegree, C (f.coeff (i + 1) * f.coeff 0 ^ i) * X ^ (i + 1)

end SparseLowFactors.BoundedDeg


