-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
-- name    : MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:19:07.733557+00:00
-- url     : https://prove2.me/theorems/056a339b-3c54-4374-bd31-b950b0abd52e
-- title:
--   Original actual norm-character H1 inclusion maps and exact-sequence predicate
-- statement:
--   For the same actual rational Picard norm kernel, retain the original global and subgroup F19-linear H1 inclusion maps from an intertwiner into the kernel representation, their restriction compatibility, and the original predicate HasExactCharacterH1Sequence. The predicate specifies exact representation maps, continuous actions on both character coefficients, and image-equals-kernel identities at the middle H1 globally and after every subgroup restriction. Its definition does not supply its witness; the named downstream consumer is the original theorem hasExactCharacterH1Sequence_of_intertwiners. All five complete original declaration types and four nonproof definition values, including the predicate formula, are compared. All seventeen original instance types and eleven nonproof instance values match, including all seven module providers. The computation law receives no extra owned theorem acceptance.
-- source:
--   Original MazurTheorem Order13ActualNormCharacterH1Exactness constructor and predicate interface, Apache-2.0. Original declaration bodies and contexts retained with the identical explicit point action; proof-valued exactness conclusions are supplied separately.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual norm-character representation sequence is exact
at the EXISTING continuous H1 globally and after restriction to every subgroup.
Named downstream consumer: kernel control for actual norm Selmer images.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterContinuousH1Data
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientInclusionData
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyCoefficientMap_restriction_coefficientMap

/- Constructor boundary: inclusion maps and the original exact-sequence predicate.
Named downstream consumer: hasExactCharacterH1Sequence_of_intertwiners. -/
noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterH1Exactness
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterH1ExactnessDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterH1ExactnessDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterH1ExactnessDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterH1ExactnessDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormCharacterH1ExactnessDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterH1ExactnessDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterH1ExactnessDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterH1ExactnessDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterH1ExactnessDataProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterH1ExactnessDataProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterH1ExactnessDataProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterH1ExactnessDataProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualNormCharacterH1ExactnessDataProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

def inclusionClass : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ) →ₗ[ZMod 19]
    ContinuousH1 K φ :=
  (inclusionH1 σ (kernelRepresentation K φ) i (by intro g m; rfl)).toZModLinearMap 19

variable (S : Subgroup (K ≃ₐ[ℚ] K))
local instance actualNormCharacterH1ExactnessDataProvider1420261018 : Module (ZMod 19) (localContinuousH1 K φ S) := restrictedH1ZModModule K φ S
local instance actualNormCharacterH1ExactnessDataProvider1520261018 : Module (ZMod 19) (ContinuousFirstCohomologyPresentation.H1 S (Coefficient σ)) :=
  restrictedCoefficientH1ZModModule σ S
local instance actualNormCharacterH1ExactnessDataProvider1620261018 : Module (ZMod 19) (ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ)) :=
  restrictedCoefficientH1ZModModule τ S
local instance actualNormCharacterH1ExactnessDataProvider1720261018 : ContinuousSMul S (Kernel K φ) := subgroup_kernelContinuousSMul K φ S

def localInclusionClass : ContinuousFirstCohomologyPresentation.H1 S (Coefficient σ) →ₗ[ZMod 19]
    localContinuousH1 K φ S :=
  (ContinuousFirstCohomologyCoefficientMap.coefficientMap S (Coefficient σ) (Kernel K φ)
    (toIntertwining σ (kernelRepresentation K φ) i)
    (fun s x => toIntertwining_equivariant σ (kernelRepresentation K φ) i
      (by intro g m; rfl) s.val x) continuous_of_discreteTopology).toZModLinearMap 19

theorem restriction_inclusionClass
    (x : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :
    restrictionLinearMap K φ S (inclusionClass K φ σ i x) =
      localInclusionClass K φ σ i S (coefficientRestriction K σ S x) :=
  ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap
    (K ≃ₐ[ℚ] K) (Coefficient σ) (Kernel K φ) (toIntertwining σ (kernelRepresentation K φ) i)
    (toIntertwining_equivariant σ (kernelRepresentation K φ) i (by intro g m; rfl))
    continuous_of_discreteTopology S x

def HasExactCharacterH1Sequence : Prop :=
  ∃ i : Representation.IntertwiningMap σ (kernelRepresentation K φ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K φ) τ,
    Function.Injective i ∧ Function.Surjective p ∧
    LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap ∧
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient σ) ∧
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient τ) ∧
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) ∧
    ∀ S : Subgroup (K ≃ₐ[ℚ] K), LinearMap.range (localInclusionClass K φ σ i S) =
      LinearMap.ker (localMapClass K φ τ p S)

end MazurTransfer.Order13ActualNormCharacterH1Exactness
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.pointsTopology
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.inclusionClass
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.localInclusionClass
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.restriction_inclusionClass
#print axioms MazurTransfer.Order13ActualNormCharacterH1Exactness.HasExactCharacterH1Sequence


