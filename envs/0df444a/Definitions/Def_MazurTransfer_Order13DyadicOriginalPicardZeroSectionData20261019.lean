-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardZeroSectionData20261019
-- name    : MazurTransfer_Order13DyadicOriginalPicardZeroSectionData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T05:33:09.368979+00:00
-- url     : https://prove2.me/theorems/c99d730d-3244-4f0f-b7c2-bd765d21c5eb
-- title:
--   Original zero section of the actual dyadic mixed quadratic curve
-- statement:
--   The exact original zero section of the actual dyadic mixed quadratic curve as a scheme morphism over its base. Its complete original type, whole section value and original prime-provider full type are independently compared. Named downstream consumer: actual dyadic Picard geometry and compatible Picard representation.
-- source:
--   MazurTheorem original mixed quadratic integral charts, overlap and gluing, by Vasily Ilin and contributors; Apache-2.0. Original attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual noetherian reduced base, proper relative curve of
dimension one, geometric integrality and a section over Z_(2).
Named downstream consumer: constructing the compatible dyadic Picard family;
its finite-map and chart-section representation inputs remain separate.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
noncomputable section
namespace MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
theorem originalDyadicPicardZeroSectionPrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩
attribute [local instance] originalDyadicPicardZeroSectionPrimeProvider20261019

def zeroSection : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of BaseRing))) (curveToBase BaseRing) :=
  ⟨Order13MixedQuadraticInfinitySections.infinitySectionZero BaseRing,
    Order13MixedQuadraticInfinitySections.infinitySectionZero_comp BaseRing⟩

end MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs
#print axioms MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.zeroSection


