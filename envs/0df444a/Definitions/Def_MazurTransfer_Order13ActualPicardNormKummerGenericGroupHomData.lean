-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData
-- name    : MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:10:45.64307+00:00
-- url     : https://prove2.me/theorems/dde421cf-a306-4926-bf7a-d04b8a9f8184
-- title:
--   Original algebraic norm Kummer homomorphism and quotient group homomorphism
-- statement:
--   Let P be the same actual rational Picard, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism with surjective K-point map. Retain the original Kummer group homomorphism from rational points and its induced quotient group homomorphism $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K)),$$ where H1 is written multiplicatively for this homomorphism. The original division and norm-image kernel laws are retained as constructor laws. All four complete original types and both constructor values are compared. The named downstream consumers are quotientHom_injective and the concrete norm Kummer group maps.
-- source:
--   Original MazurTheorem Order13ActualPicardNormKummerGroupHom generic group-homomorphism constructors and immediate laws. Complete original declaration types, constructor values and all relevant group/action dependency providers are compared. Packaged structural facts receive no extra owned theorem credit. Apache-2.0. Explicit design boundary and named downstream consumers are specified in the statement.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational norm quotient Kummer injection
preserves the group law in Mathlib algebraic H1. Continuity and local
conditions remain separate obligations.
Named downstream consumer: continuous Kummer and Selmer group bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicCohomology_classOfLift_zero_iff_rational_norm_preimage

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormKummerGroupHom
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormKummerGenericGroupHomDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKummerGenericGroupHomDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKummerGenericGroupHomDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKummerGenericGroupHomDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (hsurj : Function.Surjective (normHom K φ))
local instance actualNormKummerGenericGroupHomDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

theorem chosenClass_div (a a' : RationalPoints) :
    chosenClass K φ hsurj (a / a') = chosenClass K φ hsurj a - chosenClass K φ hsurj a' := by
  calc
    chosenClass K φ hsurj (a / a') =
      classOfLift K φ (a / a') (chosenLift K φ hsurj a / chosenLift K φ hsurj a')
        (lift_div K φ a a' _ _ (chosenLift_spec K φ hsurj a) (chosenLift_spec K φ hsurj a')) :=
      classOfLift_independent K φ _ _ _ _ _
    _ = chosenClass K φ hsurj a - chosenClass K φ hsurj a' :=
      classOfLift_div K φ a a' _ _ _ _

def kummerHom : RationalPoints →* Multiplicative (groupCohomology.H1 (kernelRep K φ)) :=
  MonoidHom.ofMapDiv (fun a => Multiplicative.ofAdd (chosenClass K φ hsurj a))
    (fun a a' => congrArg Multiplicative.ofAdd (chosenClass_div K φ hsurj a a'))

theorem rationalNormImage_le_kummerHom_kernel : (rationalNormHom φ).range ≤ (kummerHom K φ hsurj).ker := by
  rintro a ⟨c, hc⟩
  change chosenClass K φ hsurj a = 0
  exact (classOfLift_zero_iff_rational_norm_preimage K φ _ _ _).mpr ⟨c, hc⟩

def quotientHom : NormQuotient φ →* Multiplicative (groupCohomology.H1 (kernelRep K φ)) :=
  QuotientGroup.lift (rationalNormHom φ).range (kummerHom K φ hsurj)
    (rationalNormImage_le_kummerHom_kernel K φ hsurj)

end MazurTransfer.Order13ActualPicardNormKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.chosenClass_div
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.kummerHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.rationalNormImage_le_kummerHom_kernel
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.quotientHom


