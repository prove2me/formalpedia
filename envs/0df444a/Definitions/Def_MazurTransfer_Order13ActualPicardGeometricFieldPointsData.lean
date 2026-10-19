-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricFieldPointsData
-- name    : MazurTransfer_Order13ActualPicardGeometricFieldPointsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T21:30:42.757831+00:00
-- url     : https://prove2.me/theorems/ae225fd5-ce3c-4209-be89-d7bb17a0e769
-- title:
--   The original field-valued point space of the same actual rational Picard scheme
-- statement:
--   For every characteristic-zero field K, retain the original type P(K) of K-valued points of the same actual rational represented Picard scheme P, expressed as morphisms over Spec Q from the canonical K-point of Spec Q. The complete original abbreviation type and value are compared. The named downstream consumers are geometric norm preimages and the actual norm Kummer cocycles.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricNormPreimages.Points abbreviation, preserving its full type and value and the same actual represented Picard designation. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: field-valued points of the SAME existing rational
represented Picard as morphisms in the over category.
Named downstream consumers: original schemePi_geometricPoint_surjective,
schemePiConjugate_geometricPoint_surjective, and norm Kummer cocycles.
Original MazurTheorem Order13ActualPicardGeometricNormPreimages.Points.
Official Anthropic FLT Picard interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
noncomputable section
namespace MazurTransfer.Order13ActualPicardGeometricNormPreimages
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
abbrev Points (K : Type) [Field K] [CharZero K] :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase


end MazurTransfer.Order13ActualPicardGeometricNormPreimages
#print axioms MazurTransfer.Order13ActualPicardGeometricNormPreimages.Points


