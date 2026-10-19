-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData
-- name    : MazurTransfer_Order13ActualNormCharacterKummerPushforwardData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:44:39.596336+00:00
-- url     : https://prove2.me/theorems/67a94111-b8f2-438f-9306-0aa714668400
-- title:
--   Actual norm-character Kummer pushforward homomorphism
-- statement:
--   For the original actual Picard norm kernel over a characteristic-zero Galois field \(K/\mathbb Q\), retain the original finite-endomorphism and exponent-nineteen hypotheses. A coefficient intertwiner \(p\) to a representation \(\tau\), together with geometric surjectivity of the norm homomorphism, defines the pushforward \[J(\mathbb Q)/\phi J(\mathbb Q)\longrightarrow H^1_{\mathrm{cont}}(\operatorname{Aut}(K/\mathbb Q),\tau).\] It is the composition of the existing continuous Kummer homomorphism with the coefficient map, and its original evaluation law is retained. Named downstream consumer: actual norm-character Kummer kernel control. The pushforward is not asserted injective.
-- source:
--   Original MazurTheorem constructor or immediate exactness interface, Apache-2.0; complete original types and nonproof values are compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: push the existing actual norm Kummer homomorphism through
an actual coefficient intertwiner and retain its genuine good-prime inertia
vanishing. Named downstream consumer: the two ordered character Selmer images.
This coefficient pushforward carries no assertion of injectivity.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterContinuousH1Data
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData

/- Constructor boundary: the actual norm-character quotient pushforward.
Named downstream consumer: actual norm-character Kummer kernel control. -/
noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterKummerUnramified
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterKummerPushforwardDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterKummerPushforwardDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterKummerPushforwardDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterKummerPushforwardDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormCharacterKummerPushforwardDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterKummerPushforwardDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterKummerPushforwardDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterKummerPushforwardDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterKummerPushforwardDataProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterKummerPushforwardDataProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterKummerPushforwardDataProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterKummerPushforwardDataProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1
variable (hsurj : Function.Surjective (normHom K φ))

def normQuotientCharacterHom : NormQuotient φ →* Multiplicative
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  (mapClass K φ τ f).toAddMonoidHom.toMultiplicative.comp
    (continuousQuotientHom K φ hsurj)

theorem normQuotientCharacterHom_apply (a : RationalPoints) :
    (normQuotientCharacterHom K φ τ f hsurj
      (QuotientGroup.mk a : NormQuotient φ)).toAdd =
    mapClass K φ τ f (continuousClassOfLift K φ a
      (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)) := rfl

end MazurTransfer.Order13ActualNormCharacterKummerUnramified
#print axioms MazurTransfer.Order13ActualNormCharacterKummerUnramified.pointsTopology
#print axioms MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom
#print axioms MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom_apply


