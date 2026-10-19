-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
-- name    : MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:48:36.816477+00:00
-- url     : https://prove2.me/theorems/f30578f5-3c69-42c3-8e68-f5d50a9c6801
-- title:
--   Original exact norm-character Kummer sequence predicate
-- statement:
--   Retain the original actual norm data over \(K/\mathbb Q\), its two representations and geometric norm surjectivity. The predicate \(\operatorname{HasExactCharacterKummerSequence}\) requires exact intertwiners \(i,p\), middle continuous H1 exactness, and the identity \[\kappa_p(x)=1\ \Longleftrightarrow\ \exists y,\ H^1(i)(y)=\kappa_\phi(x).\] Here \(\kappa_\phi\) is the original norm Kummer class and \(\kappa_p\) its character pushforward. The predicate definition supplies no witness. Named downstream consumer: the original theorem constructing this exact Kummer sequence from specified intertwiners.
-- source:
--   Original MazurTheorem constructor or immediate exactness interface, Apache-2.0; complete original types and nonproof values are compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel of an actual norm-character Kummer pushforward
is exactly the original norm Kummer classes lifted from the character-line
continuous H1. Named downstream consumer: actual norm Selmer kernel bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData

noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterKummerKernelControl
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterKummerKernelControlProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterKummerKernelControlProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterKummerKernelControlProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterKummerKernelControlProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormCharacterKummerKernelControlProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterKummerKernelControlProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterKummerKernelControlProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterKummerKernelControlProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterKummerKernelControlProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterKummerKernelControlProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterKummerKernelControlProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterKummerKernelControlProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualNormCharacterKummerKernelControlProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
variable (hsurj : Function.Surjective (normHom K φ))

def HasExactCharacterKummerSequence : Prop :=
  ∃ i : Representation.IntertwiningMap σ (kernelRepresentation K φ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K φ) τ,
    Function.Injective i ∧ Function.Surjective p ∧
    LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap ∧
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) ∧
    ∀ x : NormQuotient φ, normQuotientCharacterHom K φ τ p hsurj x = 1 ↔
      ∃ y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ),
        inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd

end MazurTransfer.Order13ActualNormCharacterKummerKernelControl
#print axioms MazurTransfer.Order13ActualNormCharacterKummerKernelControl.pointsTopology
#print axioms MazurTransfer.Order13ActualNormCharacterKummerKernelControl.HasExactCharacterKummerSequence


