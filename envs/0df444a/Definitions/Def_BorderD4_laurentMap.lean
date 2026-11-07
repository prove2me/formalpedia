-- Prove2me | Definitions.Def_BorderD4_laurentMap
-- name    : BorderD4_laurentMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:14.757228+00:00
-- url     : https://prove2.me/theorems/dee00f60-0564-42d8-87b7-066b77293743
-- title:
--   The coefficient map $F((\varepsilon))\to E((\varepsilon))$
-- statement:
--   A field embedding $\varphi:F\to E$ induces a ring homomorphism $F((\varepsilon))\to E((\varepsilon))$ acting on coefficients, defined as the extension to fraction fields of the coefficient map $F[[\varepsilon]]\to E[[\varepsilon]]$. It is the operation of extending coefficients to the algebraic closure.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2, p.26

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The coefficientwise map `F((ε)) → E((ε))` of a field embedding `φ : F → E`, obtained as the extension
to fraction fields of the coefficientwise map `F[[ε]] → E[[ε]]`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2, p.26, where extending coefficients to the algebraic closure is the operation used. -/
noncomputable def laurentMap {F E : Type*} [Field F] [Field E] (φ : F →+* E) :
    LaurentSeries F →+* LaurentSeries E :=
  IsFractionRing.lift (A := F⟦X⟧) (K := LaurentSeries F)
    (g := (algebraMap E⟦X⟧ (LaurentSeries E)).comp (PowerSeries.map φ))
    ((IsFractionRing.injective E⟦X⟧ (LaurentSeries E)).comp
      (PowerSeries.map_injective φ φ.injective))

end BorderD4


