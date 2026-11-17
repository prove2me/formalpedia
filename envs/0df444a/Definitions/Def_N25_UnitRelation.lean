-- Prove2me | Definitions.Def_N25_UnitRelation
-- name    : N25_UnitRelation
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:39.989674+00:00
-- url     : https://prove2.me/theorems/c81534e1-01fd-4f14-9779-52c1f6fce3a1
-- title:
--   The integral algebraic relation among the modular units
-- statement:
--   The file defines the integral two-variable polynomial obtained by substituting formal variables into the unit-plane equation. It also defines a denominator-cleared expression $C(g,f_0,f_1)$ and the integral power series obtained by substituting the common denominator series and the first two numerator series. This packages the algebraic relation whose vanishing identifies $(U_0,U_0/U_1)$ with a point of the plane model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
import Definitions.Def_N25_UnitSeries
set_option autoImplicit false

noncomputable section

namespace N25

/-- The integral relation of the two normalized unit coordinates. -/
def unitRelation25 : MvPolynomial (Fin 2) ℤ :=
  planeRelation (MvPolynomial.X 0) (MvPolynomial.X 1)

/-- The relation after clearing the common denominator and the second numerator. -/
def clearedUnitRelation25
    {A : Type*} [CommRing A] (g f₀ f₁ : A) : A :=
  f₀^4*g^7 - f₀^6*g^4*f₁ +
    f₀^3*g^6*f₁^2 - f₀^5*g^4*f₁^2 -
    2*f₀^6*g^3*f₁^2 -
    f₀^4*g^4*f₁^3 - f₀^5*g^3*f₁^3 -
    2*f₀^6*g^2*f₁^3 + f₀^7*f₁^4

/-- The integral power series obtained from the cleared relation. -/
def unitRelationClearedSeries25 : PowerSeries ℤ :=
  clearedUnitRelation25 unitDenominatorSeries25
    (unitNumeratorSeries25 0) (unitNumeratorSeries25 1)

end N25


