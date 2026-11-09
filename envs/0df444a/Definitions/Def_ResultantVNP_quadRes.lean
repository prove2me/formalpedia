-- Prove2me | Definitions.Def_ResultantVNP_quadRes
-- name    : ResultantVNP_quadRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:35:43.639754+00:00
-- url     : https://prove2.me/theorems/77026dc4-d79b-47da-a987-483a01247cd0
-- title:
--   Resultant of quadratic forms $\mathrm{Res}^{(2)}_n$
-- statement:
--   The **resultant of quadratic forms** $\mathrm{Res}^{(2)}_n=\mathrm{Res}_{2,\dots,2}$ is the resultant of $n$ quadratic forms in $n$ variables, an integral polynomial in the $n\binom{n+1}{2}$ coefficient variables $u_{i,e}$ with $|e|=2$. It has degree $n2^{n-1}$ (Lemma 2.2).
--
--   Theorem 1.4 states that polynomial-size circuits for this family would imply $\mathrm{VP}=\mathrm{VNP}$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.2, p.12; Section 1.1, p.6

import Mathlib
import Definitions.Def_ResultantVNP_ResultantSystem

namespace ResultantVNP

/-- The **resultant of quadratic forms** `Res^{(2)}_n = Res_{2,…,2}` of `n` quadratic forms in `n`
variables, a polynomial in the `n·binom(n+1, 2)` coefficient variables.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.2, p.12 ("the resultant of quadratic forms, denoted Res^{(2)}_n") and Section 1.1, p.6.

**Formalization Note** Taken from a `ResultantSystem` `𝓡` (see its note); it is the resultant for
`n ≥ 1`. -/
noncomputable def quadRes (𝓡 : ResultantSystem) (n : ℕ) :
    MvPolynomial (CoeffVar (fun _ : Fin n => 2)) ℤ :=
  𝓡.res (fun _ : Fin n => 2)

end ResultantVNP


