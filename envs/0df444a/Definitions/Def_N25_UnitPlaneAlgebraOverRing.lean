-- Prove2me | Definitions.Def_N25_UnitPlaneAlgebraOverRing
-- name    : N25_UnitPlaneAlgebraOverRing
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:54.177377+00:00
-- url     : https://prove2.me/theorems/c7cb2332-c5aa-46ba-a69a-49a96bec2239
-- title:
--   The unit-plane coordinate ring and its principal open
-- statement:
--   Defines the quartic plane relation $F(u,v)∈K[u][v]$, the affine algebra $A_K=K[u,v]/(F)$, its coordinate classes $u,v$, the common denominator $h$, the principal open $A_K[h^{-1}]$, and the fraction ring of $A_K$, together with the required algebra structures. This is the technical algebraic model on which the birational maps to and from the canonical curve are regular.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! The nested polynomial presentation of the unit-plane coordinate ring. -/
namespace N25

open Polynomial

/-- The plane relation, polynomial in v with coefficients polynomial in u. -/
noncomputable def unitPlanePolynomial25C (K : Type*) [CommRing K] : Polynomial (Polynomial K) :=
  planeRelation (C X) X

/-- The affine coordinate ring of the plane relation. -/
abbrev UnitPlaneRing25C (K : Type*) [CommRing K] := AdjoinRoot (unitPlanePolynomial25C K)

/-- The first plane coordinate in the coordinate ring. -/
noncomputable def unitPlaneU25C (K : Type*) [CommRing K] : (UnitPlaneRing25C K) := algebraMap (Polynomial K) (UnitPlaneRing25C K) X

/-- The second plane coordinate in the coordinate ring. -/
noncomputable def unitPlaneV25C (K : Type*) [CommRing K] : (UnitPlaneRing25C K) := AdjoinRoot.root (unitPlanePolynomial25C K)

/-- The common principal-open denominator of the plane-to-canonical map. -/
noncomputable def unitPlaneOpenElement25C (K : Type*) [CommRing K] : (UnitPlaneRing25C K) :=
  (unitPlaneU25C K) * (unitPlaneV25C K) * planeDenominator (unitPlaneU25C K) (unitPlaneV25C K)

/-- The plane open on which both birational maps are regular. -/
abbrev UnitPlaneOpenRing25C (K : Type*) [CommRing K] := Localization.Away (unitPlaneOpenElement25C K)

/-- The semiring structure of the plane principal open. -/
noncomputable instance unitPlaneOpenSemiring25C (K : Type*) [CommRing K] : Semiring (UnitPlaneOpenRing25C K) := inferInstance

/-- The commutative semiring structure of the plane principal open. -/
noncomputable instance unitPlaneOpenCommSemiring25C (K : Type*) [CommRing K] : CommSemiring (UnitPlaneOpenRing25C K) := inferInstance

/-- Named ring structure keeps expressions in the plane open compact. -/
noncomputable instance unitPlaneOpenCommRing25C (K : Type*) [CommRing K] : CommRing (UnitPlaneOpenRing25C K) := inferInstance

/-- The plane open retains its coefficient algebra structure. -/
noncomputable instance unitPlaneOpenAlgebra25C (K : Type*) [CommRing K] : Algebra K (UnitPlaneOpenRing25C K) := inferInstance

/-- The fraction ring of the plane coordinate ring. -/
abbrev UnitPlaneFF25C (K : Type*) [CommRing K] :=
  FractionRing (UnitPlaneRing25C K)

end N25


