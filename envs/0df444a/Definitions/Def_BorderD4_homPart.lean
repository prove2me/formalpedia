-- Prove2me | Definitions.Def_BorderD4_homPart
-- name    : BorderD4_homPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:17.404556+00:00
-- url     : https://prove2.me/theorems/d8bb0c19-84c7-4693-bf34-3f71248919c5
-- title:
--   Homogeneous components $H_d(f)$
-- statement:
--   For $f\in F[[u]]$ and $d\ge 0$, $H_d(f)\in F[u]$ is the homogeneous component of $f$ of total degree $d$.
--
--   **Formalization Note** The value is a polynomial, since Theorem 6.12 multiplies it by a polynomial.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.1 "Power Series", p.29

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The homogeneous component `H_d(f) ∈ F[u]` of total degree `d` of `f ∈ F[[u]]`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2.1 "Power Series", p.29.

**Formalization Note** Mathlib's `MvPowerSeries.homogeneousComponent` returns a power series; this def returns
the polynomial, which is what Theorem 6.12 multiplies by `G_2`. -/
noncomputable def homPart {F τ : Type*} [Field F] [Fintype τ] [DecidableEq τ] (d : ℕ)
    (f : MvPowerSeries τ F) : MvPolynomial τ F :=
  ∑ m ∈ Finset.finsuppAntidiag Finset.univ d, monomial m (MvPowerSeries.coeff m f)

end BorderD4


