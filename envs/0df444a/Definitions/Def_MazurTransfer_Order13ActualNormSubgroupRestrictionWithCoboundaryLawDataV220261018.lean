-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
-- name    : MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T00:35:24.593226+00:00
-- url     : https://prove2.me/theorems/336a2f40-cddd-4fc7-b8d9-2750d4a7f736
-- title:
--   The original actual norm H1 subgroup restriction and its coboundary class law
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, phi a finite internal group endomorphism, and S any subgroup of Aut_Q(K) with its induced topology. Retain the original local continuous first-cohomology type and norm-class restriction homomorphism $$H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K))\longrightarrow H^1_{\mathrm{cont}}(S,\ker\varphi(K)).$$ For a given K-valued lift of a rational point, the restricted class is zero exactly when its restricted cocycle is a kernel coboundary. All four complete original types and three constructor values are compared, with the original group/topology/action providers. The named downstream consumer is the subgroup-invariant norm preimage criterion, followed by decomposition-group local conditions. No arithmetic identification of decomposition groups is asserted.
-- source:
--   Original MazurTheorem Order13ActualPicardNormSubgroupRestriction constructor declarations and immediate coboundary class computation, Apache-2.0. Original point action explicit and all complete original types/provider values compared. No extra owned theorem credit for the packaged class law.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of actual continuous norm classes to Galois
subgroups has zero class exactly when there is a subgroup-invariant norm
preimage. Named downstream consumer: decomposition-group local conditions.
No arithmetic identification of decomposition groups is asserted here.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologySubgroupRestriction_restriction_classMap_zero_iff
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormSubgroupRestriction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormSubgroupRestrictionDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormSubgroupRestrictionDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormSubgroupRestrictionDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormSubgroupRestrictionDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormSubgroupRestrictionDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormSubgroupRestrictionDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormSubgroupRestrictionDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormSubgroupRestrictionDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormSubgroupRestrictionDataProvider920261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ


open Order13ActualPicardNormContinuousCohomology
variable (S : Subgroup (K ≃ₐ[ℚ] K))

abbrev localContinuousH1 := ContinuousFirstCohomologyPresentation.H1 S (Kernel K φ)

def restrictNormClass : ContinuousH1 K φ →+ localContinuousH1 K φ S :=
  ContinuousFirstCohomologySubgroupRestriction.restriction (K ≃ₐ[ℚ] K) (Kernel K φ) S

theorem restrictedClass_zero_iff_subgroup_coboundary
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ S (continuousClassOfLift K φ a b hb) = 0 ↔
      ∃ z : Kernel K φ, ∀ σ : S,
        actionHom K σ.val z.val * z.val⁻¹ = difference K b σ.val := by
  rw [restrictNormClass, continuousClassOfLift]
  rw [ContinuousFirstCohomologySubgroupRestriction.restriction_classMap_zero_iff]
  change (∃ z : Kernel K φ, ∀ σ : S, σ • z / z = kernelCocycle K φ a b hb σ.val) ↔ _
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun σ => ?_⟩
    have h := congrArg Subtype.val (hz σ)
    change actionHom K σ.val z.val / z.val = difference K b σ.val at h
    simpa only [div_eq_mul_inv] using h
  · rintro ⟨z, hz⟩
    refine ⟨z, fun σ => ?_⟩
    apply Subtype.ext
    change actionHom K σ.val z.val / z.val = difference K b σ.val
    simpa only [div_eq_mul_inv] using hz σ


end MazurTransfer.Order13ActualPicardNormSubgroupRestriction
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestriction.pointsTopology
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestriction.localContinuousH1
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictNormClass
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_coboundary


