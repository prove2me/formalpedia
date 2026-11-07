-- Prove2me | Definitions.Def_CubicProductLB_offDiag
-- name    : CubicProductLB_offDiag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:10.793464+00:00
-- url     : https://prove2.me/theorems/25ade4b6-ac89-4335-9290-efe4322cd581
-- title:
--   The off-diagonal coefficient matrix $C$ of a quadratic polynomial
-- statement:
--   For a polynomial $Q$, the matrix $C$ has $C_{ij}$ equal to the coefficient of $x_i x_j$ for $i \ne j$, and $C_{ii} = 0$. For $Q$ quadratic it is symmetric, and its minors $C(I, J)$ on disjoint index sets are the objects of Lemma 9.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 5.2, p.10

import Mathlib

namespace CubicProductLB

/-- The symmetric off-diagonal coefficient matrix `C` of a polynomial: `C_ij` is the coefficient of
`x_i x_j` for `i ≠ j`, and `C_ii = 0` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 5.2, p.10). -/
noncomputable def offDiag {n : ℕ} (Q : MvPolynomial (Fin n) (ZMod 3)) :
    Matrix (Fin n) (Fin n) (ZMod 3) :=
  fun i j => if i = j then 0 else Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)

end CubicProductLB


