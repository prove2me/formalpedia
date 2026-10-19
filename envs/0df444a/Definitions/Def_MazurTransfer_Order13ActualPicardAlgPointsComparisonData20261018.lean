-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
-- name    : MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T08:52:03.287883+00:00
-- url     : https://prove2.me/theorems/0d6aa2c9-aace-4834-8169-feec859778fa
-- title:
--   The original actual Picard point-group and represented group-law comparison
-- statement:
--   For the same original actual rational Picard scheme, retain commutativity of its represented relative group law, the original additive equivalence between its scheme-valued field points and the original RelativeGroupLaw.AlgPoints carrier, and the induced equivalence on nineteen-torsion. The field is any characteristic-zero field in the exact original universe. The original two group-object providers and both equivalence values are retained and checked. Named downstream consumer: the actual geometric nineteen-torsion cardinality theorem for the represented abelian scheme.
-- source:
--   MazurTheorem, Order13ActualPicardAlgPointsComparison.lean, Apache-2.0. Three complete original declaration types, two nonproof equivalence values, two original provider types and their one nonproof group-object value checked against the original module.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual Picard point group used by the norm maps is
additively isomorphic to the original RelativeGroupLaw.AlgPoints carrier
on the SAME scheme with its represented group law.
Named downstream consumer: actual geometric nineteen-torsion cardinality.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

noncomputable section
namespace MazurTransfer.Order13ActualPicardAlgPointsComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricNormPreimages
open Order13ActualNormKernelProductCardinality
open scoped CategoryTheory.MonObj
local instance actualAlgPointsComparisonOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualAlgPointsComparisonOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj

theorem actualLaw_isCommutative : actualLaw.IsCommutative :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).relativeGroupLaw_isCommutative

variable (K : Type) [Field K] [CharZero K]

def actualAlgPointsAddEquiv :
    Additive (Points K) ≃+ actualLaw.AlgPoints actualLaw_isCommutative K where
  toFun x := Additive.ofMul (overHomToSchemeHomOver x.toMul)
  invFun x := Additive.ofMul (schemeHomOverToOverHom x.toMul)
  left_inv x := by
    change Additive.ofMul (schemeHomOverToOverHom (overHomToSchemeHomOver x.toMul)) = x
    rw [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rfl
  right_inv x := by
    change Additive.ofMul (overHomToSchemeHomOver (schemeHomOverToOverHom x.toMul)) = x
    rw [overHomToSchemeHomOver_schemeHomOverToOverHom]
    rfl
  map_add' x y := by
    change overHomToSchemeHomOver (x.toMul * y.toMul) =
      actualLaw.mul _ (overHomToSchemeHomOver x.toMul) (overHomToSchemeHomOver y.toMul)
    change overHomToSchemeHomOver (x.toMul * y.toMul) =
      overHomToSchemeHomOver (schemeHomOverToOverHom (overHomToSchemeHomOver x.toMul) *
        schemeHomOverToOverHom (overHomToSchemeHomOver y.toMul))
    rw [schemeHomOverToOverHom_overHomToSchemeHomOver,
      schemeHomOverToOverHom_overHomToSchemeHomOver]

def actualNineteenTorsionAlgPointsEquiv :
    NineteenTorsion K ≃ Submodule.torsionBy ℤ
      (actualLaw.AlgPoints actualLaw_isCommutative K) (19 : ℤ) :=
  Equiv.subtypeEquiv (actualAlgPointsAddEquiv K).toEquiv (by
    intro x
    change (19 : ℕ) • x = 0 ↔ (19 : ℤ) • actualAlgPointsAddEquiv K x = 0
    erw [natCast_zsmul, ← map_nsmul (actualAlgPointsAddEquiv K)]
    constructor
    · intro hx
      rw [hx, map_zero]
    · intro hx
      apply (actualAlgPointsAddEquiv K).injective
      simpa only [map_zero] using hx)

end MazurTransfer.Order13ActualPicardAlgPointsComparison
#print axioms MazurTransfer.Order13ActualPicardAlgPointsComparison.actualAlgPointsAddEquiv

#print axioms MazurTransfer.Order13ActualPicardAlgPointsComparison.actualNineteenTorsionAlgPointsEquiv


