-- Prove2me | Definitions.Def_N25_UnitPlaneRing
-- name    : N25_UnitPlaneRing
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:04.763345+00:00
-- url     : https://prove2.me/theorems/4f9a0f21-20ed-4633-9366-660762eaa9f7
-- title:
--   Coordinate ring and principal open of the unit-plane model
-- statement:
--   The file presents the plane equation as a polynomial in $V$ over $ℚ[U]$, defines the affine coordinate ring $$A=ℚ[U,V]/(R),$$ and names the universal coordinates $U,V∈A$. It also defines the open element $f=UV D(U,V)$ and the principal-open ring $A[f^{-1}]$, with its rational algebra structure. This is the literal algebraic model on which both birational maps are regular.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! The nested polynomial presentation of the unit-plane coordinate ring. -/
namespace N25
open Polynomial

/-- The plane relation, polynomial in v with coefficients polynomial in u. -/
noncomputable def unitPlanePolynomial : Polynomial (Polynomial ℚ) :=
  planeRelation (C X) X

/-- The affine coordinate ring of the plane relation. -/
abbrev UnitPlaneRing := AdjoinRoot unitPlanePolynomial

/-- The first plane coordinate in the coordinate ring. -/
noncomputable def unitPlaneU : UnitPlaneRing := algebraMap (Polynomial ℚ) UnitPlaneRing X

/-- The second plane coordinate in the coordinate ring. -/
noncomputable def unitPlaneV : UnitPlaneRing := AdjoinRoot.root unitPlanePolynomial

/-- The common principal-open denominator of the plane-to-canonical map. -/
noncomputable def unitPlaneOpenElement : UnitPlaneRing :=
  unitPlaneU * unitPlaneV * planeDenominator unitPlaneU unitPlaneV

/-- The plane open on which both birational maps are regular. -/
abbrev UnitPlaneOpenRing := Localization.Away unitPlaneOpenElement

/-- The semiring structure of the plane principal open. -/
noncomputable instance unitPlaneOpenSemiring : Semiring UnitPlaneOpenRing := inferInstance

/-- The commutative semiring structure of the plane principal open. -/
noncomputable instance unitPlaneOpenCommSemiring : CommSemiring UnitPlaneOpenRing := inferInstance

/-- Named ring structure keeps expressions in the plane open compact. -/
noncomputable instance unitPlaneOpenCommRing : CommRing UnitPlaneOpenRing := inferInstance

/-- The plane open retains its rational algebra structure. -/
noncomputable instance unitPlaneOpenRatAlgebra : Algebra ℚ UnitPlaneOpenRing := inferInstance

end N25


