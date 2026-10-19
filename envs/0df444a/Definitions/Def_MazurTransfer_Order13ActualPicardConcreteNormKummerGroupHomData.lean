-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardConcreteNormKummerGroupHomData
-- name    : MazurTransfer_Order13ActualPicardConcreteNormKummerGroupHomData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:22:52.629878+00:00
-- url     : https://prove2.me/theorems/53387a9e-e615-49b6-98b4-0fe43b30e0eb
-- title:
--   The two original concrete algebraic-closure norm Kummer group embeddings
-- statement:
--   Let P be the same actual rational Picard and let pi and pi-bar be its original norm endomorphisms. Retain the two original injective group homomorphisms $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1(\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q}),\ker\varphi(\overline{\mathbb Q})),$$ for phi equal to pi or pi-bar. The target is written multiplicatively for these group homomorphisms. The constructors specialize the accepted generic quotient group map; injectivity follows from its accepted generic injectivity theorem. All four original full types and both constructor values are compared. The named downstream consumer is the continuous actual norm Kummer and Selmer group bound; continuity and local conditions remain separate.
-- source:
--   Original MazurTheorem Order13ActualPicardNormKummerGroupHom concrete algebraic-closure group maps and immediate injectivity wrappers. Apache-2.0; original full types, constructor values and all relevant providers compared. Packaged wrapper facts receive no extra owned theorem credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational norm quotient Kummer injection
preserves the group law in Mathlib algebraic H1. Continuity and local
conditions remain separate obligations.
Named downstream consumer: continuous Kummer and Selmer group bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormKummerEmbeddingsData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerGroupHom_quotientHom_injective

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
local instance actualNormConcreteKummerGroupHomDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormConcreteKummerGroupHomDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormConcreteKummerGroupHomDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormConcreteKummerGroupHomDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (hsurj : Function.Surjective (normHom K φ))
local instance actualNormConcreteKummerGroupHomDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

local instance actualNormConcreteKummerGroupHomDataProvider620261017 : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois

def actualPiAlgebraicClosureKummerGroupHom :
    NormQuotient schemePi →* Multiplicative (groupCohomology.H1 (kernelRep (AlgebraicClosure ℚ) schemePi)) :=
  quotientHom (AlgebraicClosure ℚ) schemePi (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ))

theorem actualPiAlgebraicClosureKummerGroupHom_injective :
    Function.Injective actualPiAlgebraicClosureKummerGroupHom :=
  quotientHom_injective (AlgebraicClosure ℚ) schemePi
    (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ))

def actualPiConjugateAlgebraicClosureKummerGroupHom :
    NormQuotient schemePiConjugate →*
      Multiplicative (groupCohomology.H1 (kernelRep (AlgebraicClosure ℚ) schemePiConjugate)) :=
  quotientHom (AlgebraicClosure ℚ) schemePiConjugate
    (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ))

theorem actualPiConjugateAlgebraicClosureKummerGroupHom_injective :
    Function.Injective actualPiConjugateAlgebraicClosureKummerGroupHom :=
  quotientHom_injective (AlgebraicClosure ℚ) schemePiConjugate
    (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ))

end MazurTransfer.Order13ActualPicardNormKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.actualPiAlgebraicClosureKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.actualPiAlgebraicClosureKummerGroupHom_injective
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.actualPiConjugateAlgebraicClosureKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerGroupHom.actualPiConjugateAlgebraicClosureKummerGroupHom_injective


