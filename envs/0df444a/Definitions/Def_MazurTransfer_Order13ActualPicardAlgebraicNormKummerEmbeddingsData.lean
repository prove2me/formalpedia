-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormKummerEmbeddingsData
-- name    : MazurTransfer_Order13ActualPicardAlgebraicNormKummerEmbeddingsData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:11:03.69153+00:00
-- url     : https://prove2.me/theorems/7b3abf07-cc0e-4ac9-b895-19d4cefe1094
-- title:
--   The two original actual norm Kummer embeddings and their algebraic-closure specializations
-- statement:
--   Let P be the same actual rational Picard, with its original norm maps pi and pi-bar. For every algebraically closed characteristic-zero field K that is Galois over Q, retain the original embeddings of both rational norm quotients into their algebraic H1 kernel groups. Retain their original specializations to the algebraic closure of Q and the original proof that this canonical extension is Galois. All four embedding constructor values and all five complete original types are compared. The named downstream consumer is the original norm Kummer group-homomorphism module. Continuity and local conditions remain separate.
-- source:
--   Original MazurTheorem Order13ActualPicardNormAlgebraicKummerInjection concrete embedding constructors and canonicalClosureGalois. Complete original declaration types, constructor values and all relevant group/action dependency providers are compared. Packaged structural facts receive no extra owned theorem credit. Apache-2.0. Explicit design boundary and named downstream consumers are specified in the statement.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the rational quotient by an actual norm map injects
into Mathlib algebraic H1 of its actual geometric norm kernel.
Continuity and local conditions are separate obligations.
Named downstream consumer: continuous Kummer and Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicKummerInjection_quotientMap_injective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
noncomputable section
namespace MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormAlgebraicKummerEmbeddingsDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormAlgebraicKummerEmbeddingsDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormAlgebraicKummerEmbeddingsDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormAlgebraicKummerEmbeddingsDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormAlgebraicKummerEmbeddingsDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

variable [IsAlgClosed K]

def actualPiKummerInjection : NormQuotient schemePi ↪ groupCohomology.H1 (kernelRep K schemePi) :=
  ⟨quotientMap K schemePi (schemePi_geometricPoint_surjective K),
    quotientMap_injective K schemePi (schemePi_geometricPoint_surjective K)⟩

def actualPiConjugateKummerInjection :
    NormQuotient schemePiConjugate ↪ groupCohomology.H1 (kernelRep K schemePiConjugate) :=
  ⟨quotientMap K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K),
    quotientMap_injective K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K)⟩


theorem canonicalClosureGalois : IsGalois ℚ (AlgebraicClosure ℚ) := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    have h : (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ)) =
        @AlgebraicClosure.instAlgebra ℚ inferInstance ℚ inferInstance (Algebra.id ℚ) :=
      Subsingleton.elim _ _
    rw [h]
    infer_instance
  exact { to_isSeparable := inferInstance, to_normal := inferInstance }

def actualPiAlgebraicClosureKummerInjection :
    NormQuotient schemePi ↪ groupCohomology.H1 (kernelRep (AlgebraicClosure ℚ) schemePi) := by
  letI : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
  exact actualPiKummerInjection (AlgebraicClosure ℚ)

def actualPiConjugateAlgebraicClosureKummerInjection :
    NormQuotient schemePiConjugate ↪
      groupCohomology.H1 (kernelRep (AlgebraicClosure ℚ) schemePiConjugate) := by
  letI : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
  exact actualPiConjugateKummerInjection (AlgebraicClosure ℚ)

end MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.actualPiKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.actualPiConjugateKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.actualPiAlgebraicClosureKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.actualPiConjugateAlgebraicClosureKummerInjection


