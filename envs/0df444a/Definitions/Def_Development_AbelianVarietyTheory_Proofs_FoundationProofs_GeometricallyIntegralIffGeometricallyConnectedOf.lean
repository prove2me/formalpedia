-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:08.854804+00:00
-- url     : https://prove2.me/theorems/433553b7-f24b-4012-8b0b-66bf8697be10
-- title:
--   Geometrically Integral Iff Geometrically Connected Of
-- statement:
--   Definitions and structural lemmas for Geometrically Integral Iff Geometrically Connected Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeometricallyIntegralIffGeometricallyConnectedOf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
namespace GlobalTheory
section Morphisms
variable {X Y S : Scheme.{u}}
end Morphisms
section Products
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}}
open ReciprocityTheory.ChartRestriction.G.Semi
variable (G : Over S) [Smooth G.hom]
variable [GeometricallyConnected G.hom]
end Products
section Powers
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} (G : Over S) [Smooth G.hom]
variable [GeometricallyConnected G.hom]
end Powers
section Local
variable {X : Scheme.{u}} {V : Type u} [CommRing V]
end Local
section Groups
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{u}}
end Groups
section Main
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
end Main
end GlobalTheory


