-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData
-- name    : MazurTransfer_Order13ActualNormContinuousH1ClassData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T23:56:05.519316+00:00
-- url     : https://prove2.me/theorems/cc21436a-1b23-4556-b1cf-73a02560d5c6
-- title:
--   The original actual finite norm continuous cocycle class
-- statement:
--   Let P be the same actual rational Picard, K a characteristic-zero Galois extension of Q, and phi a finite internal group endomorphism. A K-valued preimage b of a rational point a determines the continuous kernel cocycle sigma mapping to sigma(b)b inverse, and hence a class $$[b]_{\mathrm{cont}}\in H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(K),\ker(\varphi)(K)).$$ Retain the original coefficient topology, continuous H1 type, cocycle and class constructors. The forgetful map sends this continuous class to its original algebraic H1 class. All five complete original types and four constructor values are compared, along with the original group/topology/action providers. Named downstream consumers are the continuous norm class zero criterion and the continuous norm quotient Kummer group injection. Local Selmer conditions and comparison to Mathlib homological continuous cohomology remain separate.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousCohomology constructor types and values, plus its immediate forgetful class law. Apache-2.0. Point-action providers are given by the original explicit structure constructor and checked definitionally; no extra owned credit for packaged laws.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual continuous kernel cocycles determine classes
in continuous H1, defined as continuous cocycles modulo coboundaries.
These classes have an injective forgetful map to Mathlib algebraic H1.
Named downstream consumer: actual continuous Kummer quotient injections.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernelCocycle_continuous
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormContinuousCohomology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormContinuousH1ClassDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormContinuousH1ClassDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormContinuousH1ClassDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormContinuousH1ClassDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormContinuousH1ClassDataProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormContinuousH1ClassDataProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormContinuousH1ClassDataProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormContinuousH1ClassDataProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormContinuousH1ClassDataProvider920261017 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ

abbrev ContinuousH1 := ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Kernel K φ)

def continuousCocycle (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    ContinuousFirstCohomologyPresentation.continuousCocycles (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  ⟨cocycle K φ a b hb, kernelCocycle_continuous K φ a b hb⟩

def continuousClassOfLift (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    ContinuousH1 K φ :=
  ContinuousFirstCohomologyPresentation.classMap (K ≃ₐ[ℚ] K) (Kernel K φ)
    (continuousCocycle K φ a b hb)

@[simp] theorem forget_continuousClassOfLift (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    ContinuousFirstCohomologyPresentation.forgetH1 (K ≃ₐ[ℚ] K) (Kernel K φ)
      (continuousClassOfLift K φ a b hb) = classOfLift K φ a b hb := rfl


end MazurTransfer.Order13ActualPicardNormContinuousCohomology
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCohomology.pointsTopology
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCohomology.ContinuousH1
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCohomology.continuousCocycle
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCohomology.continuousClassOfLift
#print axioms MazurTransfer.Order13ActualPicardNormContinuousCohomology.forget_continuousClassOfLift


