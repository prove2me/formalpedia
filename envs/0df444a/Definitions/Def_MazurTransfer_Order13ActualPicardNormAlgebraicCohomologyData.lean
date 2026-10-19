-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
-- name    : MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T22:15:58.530803+00:00
-- url     : https://prove2.me/theorems/f747b05b-0bc6-4018-83ef-e8d8755b46d5
-- title:
--   Original algebraic H1 representation, cocycle and lift class for actual Picard norms
-- statement:
--   Let P be the same actual rational Picard group scheme, K a characteristic-zero field, and phi an internal monoid endomorphism. Retain the original integral representation attached to the field-automorphism action on its geometric kernel, the one-cocycle attached to a norm preimage of a rational point, and its class $$[c_b]\in H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K)).$$ All three complete original constructor types and values are compared, with the original group and action providers and both dependency-provider packages. This is algebraic group cohomology. The named downstream consumers are the zero-class criterion for rational norm preimages and the rational norm quotient Kummer injection.
-- source:
--   Original MazurTheorem Order13ActualPicardNormAlgebraicCohomology kernelRep, cocycle and classOfLift constructors, Apache-2.0. Design boundary: the original actual norm kernel as a Mathlib integral representation and its algebraic H1 lift class. Named downstream consumers: classOfLift_zero_iff_rational_norm_preimage and the rational norm quotient Kummer injection.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm preimages define classes in Mathlib H1
of the actual geometric norm kernel. Zero classes are precisely rational
norm images. This is algebraic group cohomology; continuity is separate.
Named downstream consumer: the rational norm quotient Kummer injection.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormAlgebraicCohomologyDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormAlgebraicCohomologyDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormAlgebraicCohomologyDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormAlgebraicCohomologyDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormAlgebraicCohomologyDataProvider520261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

abbrev kernelRep : Rep ℤ (K ≃ₐ[ℚ] K) :=
  Rep.ofMulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ)

def cocycle (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    groupCohomology.cocycles₁ (kernelRep K φ) :=
  groupCohomology.cocyclesOfIsMulCocycle₁ (fun σ τ => by
    rw [mul_comm]
    exact kernelCocycle_law K φ a b hb σ τ)

def classOfLift (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    groupCohomology.H1 (kernelRep K φ) :=
  groupCohomology.H1π (kernelRep K φ) (cocycle K φ a b hb)

end MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.kernelRep
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.cocycle
#print axioms MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.classOfLift


