-- Prove2me | Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
-- name    : MazurTransfer_GaloisFixedOverPointScalarExtensionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T21:59:20.036978+00:00
-- url     : https://prove2.me/theorems/60dd2ead-9302-418f-bc2a-1e02a5df139e
-- title:
--   The original scalar-extension morphism in the over category
-- statement:
--   For any field extension K/F, retain the original canonical morphism from Spec K to Spec F as a morphism in the category of schemes over Spec F. Its complete original type and constructor value are preserved. The named downstream consumers are injectivity of scalar extension on over-category points and unique descent of Galois-fixed points.
-- source:
--   Original MazurTheorem GaloisFixedOverPointDescent.scalarOverMap, Apache-2.0. Design boundary: the canonical base-change point morphism in the over category. Named downstream consumers: original scalarExtension_injective and exists_unique_descent, then the actual Picard rational-point descent bridge.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: fixed points over a Galois extension descend uniquely
as points over the base, preserving the given structure morphism.
Named downstream consumer: rational points of the actual Picard and
injectivity of the algebraic norm Kummer map.
-/
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
noncomputable section
namespace MazurTransfer.GaloisFixedOverPointDescent
open CategoryTheory AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction
variable (F K : Type) [Field F] [Field K] [Algebra F K]
abbrev scalarOverMap : Over.mk (fieldBase F K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of F))) :=
  Over.homMk (fieldBase F K) (by simp)

end MazurTransfer.GaloisFixedOverPointDescent
#print axioms MazurTransfer.GaloisFixedOverPointDescent.scalarOverMap


