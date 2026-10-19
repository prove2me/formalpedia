-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormCharacterContinuousH1Data
-- name    : MazurTransfer_Order13ActualNormCharacterContinuousH1Data
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:48:23.944075+00:00
-- url     : https://prove2.me/theorems/6545135c-830d-4ddd-a78c-6b0e685d5527
-- title:
--   Original F19-linear continuous H1 maps for actual norm-character intertwiners
-- statement:
--   For the same actual rational Picard, its original arithmetic Galois action, an arbitrary finite internal norm endomorphism phi with the original exponent-nineteen kernel fact, a representation tau over F19 and an intertwiner f from the actual kernel representation to tau, retain the original coefficient homomorphism, F19-linear global and subgroup H1 maps, coefficient restriction, and pushed norm cocycle. Retain the original equivariance, surjective-target continuity, restriction-compatibility, zero-restriction and cocycle-value laws. All twelve original declaration types and six nonproof constructor values are compared. All fourteen original local instance types and nine nonproof instance values are compared, including all five module providers. These are constructors and checked immediate computation/specialization facts, without extra owned theorem acceptances. Named downstream consumers are the original two ordered norm-character Kummer images and their good-prime inertia restrictions. The existence of the required arithmetic character intertwiners and the arithmetic inertia conditions remain separate.
-- source:
--   Original MazurTheorem Order13ActualNormCharacterContinuousH1, Apache-2.0. Original declaration bodies and complete contexts retained. The original point action is written as its identical explicit structure. Original anonymous instance declarations are matched to public providers by their source ranges and full original types and values.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm-kernel intertwiners induce F19-linear maps on
its existing continuous H1, with the original arithmetic Galois action.
Named downstream consumer: the two ordered character Kummer images and
their good-prime inertia restriction conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousCoefficientExponentF19ModuleData
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19GenericData
import Theorems.Thm_MazurTransfer_ContinuousCoefficientExponentAndContinuity_quotient_continuousSMul
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul

noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterContinuousH1
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterContinuousH1DataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterContinuousH1DataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterContinuousH1DataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterContinuousH1DataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormCharacterContinuousH1DataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterContinuousH1DataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterContinuousH1DataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterContinuousH1DataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterContinuousH1DataProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterContinuousH1DataProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterContinuousH1DataProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterContinuousH1DataProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

def coefficientHom : Kernel K φ →* Coefficient τ :=
  fromIntertwining (kernelRepresentation K φ) τ f

theorem coefficientHom_equivariant (σ : K ≃ₐ[ℚ] K) (m : Kernel K φ) :
    coefficientHom K φ τ f (σ • m) = σ • coefficientHom K φ τ f m :=
  fromIntertwining_equivariant (kernelRepresentation K φ) τ f (by intro σ m; rfl) σ m

theorem coefficient_continuousSMul (hf : Function.Surjective f) :
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient τ) :=
  quotient_continuousSMul (kernelRepresentation K φ) τ f (by intro σ m; rfl) hf

def mapClass : ContinuousH1 K φ →ₗ[ZMod 19]
    ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ) :=
  (mapH1 (kernelRepresentation K φ) τ f (by intro σ m; rfl)).toZModLinearMap 19

variable (S : Subgroup (K ≃ₐ[ℚ] K))
local instance actualNormCharacterContinuousH1DataProvider1320261018 : Module (ZMod 19) (localContinuousH1 K φ S) := restrictedH1ZModModule K φ S
local instance actualNormCharacterContinuousH1DataProvider1420261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ)) :=
  restrictedCoefficientH1ZModModule τ S

def localMapClass : localContinuousH1 K φ S →ₗ[ZMod 19]
    ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ) :=
  (localMapH1 (kernelRepresentation K φ) τ f (by intro σ m; rfl) S).toZModLinearMap 19

def coefficientRestriction :
    ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ) →ₗ[ZMod 19]
      ContinuousFirstCohomologyPresentation.H1 S (Coefficient τ) :=
  (ContinuousFirstCohomologySubgroupRestriction.restriction
    (K ≃ₐ[ℚ] K) (Coefficient τ) S).toZModLinearMap 19

theorem restriction_mapClass (x : ContinuousH1 K φ) :
    coefficientRestriction K τ S (mapClass K φ τ f x) =
      localMapClass K φ τ f S (restrictionLinearMap K φ S x) :=
  restriction_mapH1 (kernelRepresentation K φ) τ f (by intro σ m; rfl) S x

theorem restriction_zero_of_source_zero (x : ContinuousH1 K φ)
    (hx : restrictionLinearMap K φ S x = 0) :
    coefficientRestriction K τ S (mapClass K φ τ f x) = 0 := by
  rw [restriction_mapClass, hx, map_zero]

variable (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)

def pushedCocycle : ContinuousFirstCohomologyPresentation.continuousCocycles
    (K ≃ₐ[ℚ] K) (Coefficient τ) :=
  ContinuousFirstCohomologyCoefficientMap.mapContinuousCocycles
    (K ≃ₐ[ℚ] K) (Kernel K φ) (Coefficient τ) (coefficientHom K φ τ f)
    (coefficientHom_equivariant K φ τ f) continuous_of_discreteTopology
    (continuousCocycle K φ a b hb)

theorem pushedCocycle_apply (σ : K ≃ₐ[ℚ] K) :
    (Additive.toMul ((pushedCocycle K φ τ f a b hb).val σ)).val =
      f (Additive.ofMul (kernelCocycle K φ a b hb σ)) := rfl

theorem mapClass_classOfLift :
    mapClass K φ τ f (continuousClassOfLift K φ a b hb) =
      ContinuousFirstCohomologyPresentation.classMap (K ≃ₐ[ℚ] K) (Coefficient τ)
        (pushedCocycle K φ τ f a b hb) := rfl

end MazurTransfer.Order13ActualNormCharacterContinuousH1
#print axioms MazurTransfer.Order13ActualNormCharacterContinuousH1.mapClass
#print axioms MazurTransfer.Order13ActualNormCharacterContinuousH1.restriction_mapClass
#print axioms MazurTransfer.Order13ActualNormCharacterContinuousH1.mapClass_classOfLift


