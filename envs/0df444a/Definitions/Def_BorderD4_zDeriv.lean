-- Prove2me | Definitions.Def_BorderD4_zDeriv
-- name    : BorderD4_zDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:39.323911+00:00
-- url     : https://prove2.me/theorems/ed8d9099-733f-4d5f-978b-4800c712822b
-- title:
--   The derivation $\partial_z$ and $\mathrm{dlog}_z$
-- statement:
--   On the fraction field of $F[[\varepsilon]][u][[z]]$, $\partial_z$ is defined by the quotient rule from term-by-term differentiation in $z$, and $\mathrm{dlog}_z(h)=(\partial_z h)/h$.
--
--   **Formalization Note** The value is computed from the numerator and denominator chosen by `IsLocalization.sec`; the quotient rule makes it independent of the choice.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.4, p.68

import Mathlib
import Definitions.Def_BorderD4_Psi
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {F τ : Type*} [Field F]

/-- The derivation `∂_z` on the fraction field of `F[[ε]][u][[z]]`, by the quotient rule from term-by-term
differentiation in `z` on the ring. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.4 "Differentiation", p.68.

**Formalization Note** The numerator and denominator are the ones chosen by `IsLocalization.sec`; the quotient
rule makes the value independent of the choice. On `F[[ε]][u][[z]]` this is `PowerSeries.derivative`. -/
noncomputable def zDeriv (A : ZFrac F τ) : ZFrac F τ :=
  let s := IsLocalization.sec (nonZeroDivisors (ZRing F τ)) A
  algebraMap (ZRing F τ) (ZFrac F τ)
      (PowerSeries.derivative _ s.1 * (s.2 : ZRing F τ) -
        s.1 * PowerSeries.derivative _ (s.2 : ZRing F τ)) /
    algebraMap (ZRing F τ) (ZFrac F τ) (s.2 : ZRing F τ) ^ 2

/-- `dlog_z(h) = (∂_z h)/h`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.4 "Differentiation", p.68. -/
noncomputable def dlogZ (A : ZFrac F τ) : ZFrac F τ := zDeriv A / A

end

end BorderD4


