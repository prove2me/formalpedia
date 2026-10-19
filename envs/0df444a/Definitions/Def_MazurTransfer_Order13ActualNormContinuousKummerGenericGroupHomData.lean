-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData
-- name    : MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T00:08:00.566952+00:00
-- url     : https://prove2.me/theorems/5e6056d6-0ead-472a-a6c1-dbc14ab5151b
-- title:
--   The original actual norm quotient Kummer homomorphism into continuous H1
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism whose K-point map is surjective. Retain the original continuous Kummer homomorphism and its induced quotient group homomorphism $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(K),\ker(\varphi)(K)).$$ The target is written multiplicatively for these group homomorphisms. The forgetful map recovers the original algebraic norm quotient homomorphism. Retain the original chosen continuous class, coefficient topology and immediate division, kernel and forgetful laws. All eight complete original types and four constructor values are compared, with the original group/topology/action and relevant algebraic dependency providers. The named downstream consumer is the original continuousQuotientHom_injective and its two concrete actual norm specializations.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousKummerInjection generic constructor declarations and immediate laws, Apache-2.0. Original point-action structure explicit and compared in full type and value. Packaged laws receive no extra owned theorem credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational norm quotients inject by group
homomorphisms into continuous H1 of the actual geometric norm kernels.
The checked forgetful maps recover the prior algebraic Kummer maps.
Named downstream consumer: the local Selmer conditions and rank-zero bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCohomology_continuousClassOfLift_zero_iff_rational_preimage
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormContinuousKummerInjection
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormContinuousKummerGenericGroupHomDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormContinuousKummerGenericGroupHomDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormContinuousKummerGenericGroupHomDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormContinuousKummerGenericGroupHomDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormContinuousKummerGenericGroupHomDataProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormContinuousKummerGenericGroupHomDataProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormContinuousKummerGenericGroupHomDataProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormContinuousKummerGenericGroupHomDataProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormContinuousKummerGenericGroupHomDataProvider920261017 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ


variable (hsurj : Function.Surjective (normHom K φ))

def chosenContinuousClass (a : RationalPoints) : ContinuousH1 K φ :=
  continuousClassOfLift K φ a (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

@[simp] theorem forget_chosenContinuousClass (a : RationalPoints) :
    ContinuousFirstCohomologyPresentation.forgetH1 (K ≃ₐ[ℚ] K) (Kernel K φ)
      (chosenContinuousClass K φ hsurj a) = chosenClass K φ hsurj a := rfl

theorem chosenContinuousClass_div (a a' : RationalPoints) :
    chosenContinuousClass K φ hsurj (a / a') =
      chosenContinuousClass K φ hsurj a - chosenContinuousClass K φ hsurj a' := by
  apply ContinuousFirstCohomologyPresentation.forgetH1_injective (K ≃ₐ[ℚ] K) (Kernel K φ)
  simp only [map_sub, forget_chosenContinuousClass]
  exact Order13ActualPicardNormKummerGroupHom.chosenClass_div K φ hsurj a a'

def continuousKummerHom : RationalPoints →* Multiplicative (ContinuousH1 K φ) :=
  MonoidHom.ofMapDiv (fun a => Multiplicative.ofAdd (chosenContinuousClass K φ hsurj a))
    (fun a a' => congrArg Multiplicative.ofAdd (chosenContinuousClass_div K φ hsurj a a'))

theorem rationalNormImage_le_continuousKummerHom_kernel :
    (rationalNormHom φ).range ≤ (continuousKummerHom K φ hsurj).ker := by
  rintro a ⟨c, hc⟩
  change chosenContinuousClass K φ hsurj a = 0
  exact (continuousClassOfLift_zero_iff_rational_preimage K φ a _ _).mpr ⟨c, hc⟩

def continuousQuotientHom : NormQuotient φ →* Multiplicative (ContinuousH1 K φ) :=
  QuotientGroup.lift (rationalNormHom φ).range (continuousKummerHom K φ hsurj)
    (rationalNormImage_le_continuousKummerHom_kernel K φ hsurj)

theorem continuousQuotientHom_forget (x : NormQuotient φ) :
    ContinuousFirstCohomologyPresentation.forgetH1 (K ≃ₐ[ℚ] K) (Kernel K φ)
      (continuousQuotientHom K φ hsurj x).toAdd =
    (Order13ActualPicardNormKummerGroupHom.quotientHom K φ hsurj x).toAdd := by
  refine Quotient.inductionOn x ?_
  intro a
  rfl


end MazurTransfer.Order13ActualPicardNormContinuousKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.pointsTopology
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.chosenContinuousClass
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.forget_chosenContinuousClass
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.chosenContinuousClass_div
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousKummerHom
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.rationalNormImage_le_continuousKummerHom_kernel
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom_forget


