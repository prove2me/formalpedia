-- Prove2me | Definitions.Def_ResultantVNP_Supplement_coeffFamily
-- name    : ResultantVNP_Supplement_coeffFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:57:05.40509+00:00
-- url     : https://prove2.me/theorems/69ff90cd-d8dd-40fd-bd10-74de08122cda
-- title:
--   The coefficient family $\{\Phi_{5m^2,m^2}(A)\}_{m\ge3}$ as a polynomial family
-- statement:
--   Let $A$ be the generic symmetric cubic tensor of dimension $N$, with one independent variable for each unordered triple of indices, and let $\Phi_{N,s}(A)=[z^s]\,\mathrm{Det}_N(I+zA)$ be its characteristic coefficient polynomial. The **coefficient family** is
--   $$\bigl\{\Phi_{5m^2,\,m^2}(A)\bigr\}_{m\ge3},$$
--   viewed as a family of complex polynomials. Its member with index $n$ is $\Phi_{5m^2,m^2}$ with $m=n+3$; its variables, one per unordered triple of $[5m^2]$, are numbered by a fixed bijection.
--
--   This is the family whose VNP-completeness is Theorem 1.7.
--
--   **Formalization Note** Polynomial families of the base mission are indexed by every $n\in\mathbb N$, so the index set $m\ge3$ is encoded by the shift $m=n+3$; polynomial bounds in $n$ and in $m$ are the same.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.7, p.6; Definition 3.1, p.14

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_PolyFamily

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

/-- **The coefficient family `{Φ_{5m², m²}(A)}_{m ≥ 3}` as a polynomial family.** Member number
`n` is `Φ_{5m², m²}` with `m = n + 3`, on the generic symmetric cubic tensor `A` of dimension `5m²`
(one variable per unordered triple of indices), mapped from `ℤ` to `ℂ`; its variables are numbered
`0, …, |Sym(Fin(5m²), 3)| − 1` by a fixed bijection.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.7, p.6 ("Let A be
a generic symmetric tensor of order three. The family {Φ_{5m²,m²}(A)}_{m≥3}"); Definition 3.1, p.14.

**Formalization Note** `PolyFamily` is indexed by all `n ∈ ℕ`, so the index set `m ≥ 3` is encoded
by the shift `m = n + 3`; this changes no polynomial bound. The variable numbering is
`Fintype.equivFin`; VNP membership is invariant under renaming variables. -/
noncomputable def coeffFamily (𝓡 : ResultantSystem) : PolyFamily where
  nvars n := Fintype.card (Sym (Fin (5 * (n + 3) ^ 2)) 3)
  p n := MvPolynomial.rename (Fintype.equivFin (Sym (Fin (5 * (n + 3) ^ 2)) 3))
    (MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * (n + 3) ^ 2) ((n + 3) ^ 2)))

end Supplement

end ResultantVNP


