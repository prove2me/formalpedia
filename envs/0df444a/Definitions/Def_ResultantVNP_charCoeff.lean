-- Prove2me | Definitions.Def_ResultantVNP_charCoeff
-- name    : ResultantVNP_charCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:38:22.843678+00:00
-- url     : https://prove2.me/theorems/1b8ebb83-d6e2-41a6-8ae0-b5e951048deb
-- title:
--   Characteristic coefficient $\Phi_{n,s}(A)=[z^s]\,\mathrm{Det}_n(I+zA)$
-- statement:
--   Let $I_{ijk}=\delta_{i,j,k}$ be the diagonal unit tensor of dimension $n$ and $A$ a symmetric cubic tensor of dimension $n$ with one variable per unordered triple of indices. The **characteristic coefficient polynomial** is
--
--   $$
--   \Phi_{n,s}(A):=[z^s]\,\mathrm{Det}_n(I+zA),
--   $$
--
--   the coefficient of $z^s$ in $\mathrm{Det}_n(I+zA)$ viewed as a polynomial in $z$. It is an integral polynomial in the entries of $A$, homogeneous of degree $s$.
--
--   The family $\{\Phi_{5m^2,m^2}\}_{m\ge3}$ is the VNP-hard family of Theorem 3.2.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Definition 3.1, Eq. (3), p.14

import Mathlib
import Definitions.Def_ResultantVNP_symTensorDet

namespace ResultantVNP

/-- The **characteristic coefficient polynomial** `Φ_{n,s}(A) := [z^s] Det_n(I + zA)`: the coefficient
of `z^s` in the tensor determinant of `I + zA`, where `I_{ijk} = δ_{i,j,k}` is the diagonal unit tensor
and `A` is a symmetric cubic tensor of dimension `n` with one variable per unordered triple of indices.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Definition 3.1, Eq. (3), p.14.

**Formalization Note** Computed in `(ℤ[a_T])[z]`: every variable `a_T` of `symTensorDet` is replaced by
`δ_T + z·a_T` (`δ_T = 1` iff `T = {i,i,i}` for some `i`, else `0`) and the coefficient of `z^s` is
taken. Meaningful for `n ≥ 1` (see `ResultantSystem`). -/
noncomputable def charCoeff (𝓡 : ResultantSystem) (n s : ℕ) : MvPolynomial (Sym (Fin n) 3) ℤ :=
  (MvPolynomial.aeval
      (fun T : Sym (Fin n) 3 =>
        Polynomial.C (if ∃ i, T = Sym.replicate 3 i then (1 : MvPolynomial (Sym (Fin n) 3) ℤ) else 0) +
          Polynomial.X * Polynomial.C (MvPolynomial.X T))
      (symTensorDet 𝓡 n)).coeff s

end ResultantVNP


