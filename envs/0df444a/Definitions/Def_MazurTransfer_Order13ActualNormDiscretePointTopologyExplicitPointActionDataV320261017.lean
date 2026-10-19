-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormDiscretePointTopologyExplicitPointActionDataV320261017
-- name    : MazurTransfer_Order13ActualNormDiscretePointTopologyExplicitPointActionDataV320261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:39:18.257787+00:00
-- url     : https://prove2.me/theorems/c006aaac-6f9a-4cb4-994b-1718c7750426
-- title:
--   The original discrete geometric point topology for actual norm cocycles
-- statement:
--   Let P be the same actual rational Picard and K a characteristic-zero field. Equip its K-valued points with the discrete topology. Retain the original constructor for this topology and the original group, point action and kernel action providers. The automorphism group retains its canonical Krull topology. The named downstream consumers are continuity of the actual norm-kernel action and the kernel-valued preimage cocycle. This package defines coefficient topology and actions; the continuity theorems are separate obligations.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousCocycles.pointsTopology and its complete original geometric point topology/group/action provider values. Apache-2.0; the complete original constructor type and value and all four nonproof providers are compared. The original point action structure is given explicitly; it is compared in full type and value against the original provider.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm fibres give continuous cocycles for the
Krull topology and discrete geometric kernel topology. Named downstream
consumer: continuous Kummer classes and the local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_FiniteRationalFibreGaloisOrbit_stabilizer_isOpen

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormContinuousCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormContinuousPointTopologyDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormContinuousPointTopologyDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormContinuousPointTopologyDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormContinuousPointTopologyDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormContinuousPointTopologyDataProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormContinuousPointTopologyDataProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormContinuousPointTopologyDataProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormContinuousPointTopologyDataProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

end MazurTransfer.Order13ActualPicardNormContinuousCocycles
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCocycles.pointsTopology


