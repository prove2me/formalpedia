-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
-- name    : MazurTransfer_Order13DyadicMixedOriginalAffineChartData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:25:54.610785+00:00
-- url     : https://prove2.me/theorems/96b5142c-66ad-413f-bb0a-e876f44f8077
-- title:
--   Original actual dyadic mixed affine chart constructors
-- statement:
--   Seven original constructors for the literal mixed quadratic coordinate algebras, affine schemes and structural morphisms over the integers localized at two. All seven complete types and whole values, and the original prime-two provider type, are independently compared with the source. Named downstream consumers: the actual dyadic affine chart geometry and proper gluing.
-- source:
--   MazurTheorem Order13DyadicMixedQuadraticCharts, original BaseRing, coordinate rings, Spec charts and structural morphisms; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual ordinary and reciprocal affine mixed quadratic
schemes over Z localized at two, both smooth, flat and locally finitely
presented. Named downstream consumer: their gluing and comparison with
the existing rational order-thirteen curve. Proper gluing is separate.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
import Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps

noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticCharts
open CategoryTheory AlgebraicGeometry
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13LocalIntegralCoefficientMaps
local instance dyadicChartOriginalPrimeTwoProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev BaseRing := LocalRing 2

universe u
variable (R : Type u) [CommRing R]
abbrev ordinaryCoordinateRing := CoordinateRing R (ordinaryH R) (ordinaryF R)
abbrev reciprocalCoordinateRing := CoordinateRing R (reciprocalH R) (reciprocalF R)

def ordinaryScheme : Scheme := Scheme.Spec.obj (.op (.of (ordinaryCoordinateRing R)))
def reciprocalScheme : Scheme := Scheme.Spec.obj (.op (.of (reciprocalCoordinateRing R)))
def ordinaryToBase : ordinaryScheme R ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryCoordinateRing R)))
def reciprocalToBase : reciprocalScheme R ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (reciprocalCoordinateRing R)))

end MazurTransfer.Order13DyadicMixedQuadraticCharts
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.BaseRing
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.ordinaryCoordinateRing
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.reciprocalCoordinateRing
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.ordinaryScheme
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.reciprocalScheme
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.ordinaryToBase
#print axioms MazurTransfer.Order13DyadicMixedQuadraticCharts.reciprocalToBase


