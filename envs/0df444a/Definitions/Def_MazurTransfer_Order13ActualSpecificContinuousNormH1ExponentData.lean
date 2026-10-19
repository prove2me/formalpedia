-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualSpecificContinuousNormH1ExponentData
-- name    : MazurTransfer_Order13ActualSpecificContinuousNormH1ExponentData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:08:02.712543+00:00
-- url     : https://prove2.me/theorems/8eb58344-7c4f-453f-a8d4-a7b7efc27009
-- title:
--   Original exponent-nineteen facts for both actual continuous norm H1 groups
-- statement:
--   For the same actual rational Picard and its two original norm maps, specialize the exponent-nineteen continuous H1 theorem over the algebraic closure of Q. Retain the original discrete point-topology constructor and the two specialization facts. All three complete original types and the one nonproof constructor value are compared, together with relevant original group/topology/action providers and the two complete finite-map proposition types. The named downstream consumers are the exponent of the actual rational norm quotients and F19 modules. No finiteness or rank is asserted.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousH1Exponent, Apache-2.0. Original constructors and immediate specialization/computation facts retain their full original types. Packaged proof-valued facts receive no extra owned theorem credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualConcreteContinuousNormKummerGroupHomData
import Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousH1Exponent_continuousH1_killed_nineteen

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormContinuousH1Exponent
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormSpecificContinuousH1ExponentDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormSpecificContinuousH1ExponentDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormSpecificContinuousH1ExponentDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormSpecificContinuousH1ExponentDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormSpecificContinuousH1ExponentDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormSpecificContinuousH1ExponentDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormSpecificContinuousH1ExponentDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormSpecificContinuousH1ExponentDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormSpecificContinuousH1ExponentDataProvider920261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ



local instance actualNormSpecificContinuousH1ExponentDataProvider1020261018 : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
open Order13ActualPicardNormContinuousKummerInjection
local instance actualNormSpecificContinuousH1ExponentDataProvider1120261018 : IsFinite schemePi.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance actualNormSpecificContinuousH1ExponentDataProvider1220261018 : IsFinite schemePiConjugate.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1

theorem actualPiContinuousH1_killed_nineteen (x : ContinuousH1 (AlgebraicClosure ℚ) schemePi) :
    (19 : ℕ) • x = 0 :=
  continuousH1_killed_nineteen (AlgebraicClosure ℚ) schemePi
    (pi_kernel_exponent_nineteen (AlgebraicClosure ℚ)) x

theorem actualPiConjugateContinuousH1_killed_nineteen
    (x : ContinuousH1 (AlgebraicClosure ℚ) schemePiConjugate) : (19 : ℕ) • x = 0 :=
  continuousH1_killed_nineteen (AlgebraicClosure ℚ) schemePiConjugate
    (piConjugate_kernel_exponent_nineteen (AlgebraicClosure ℚ)) x


end MazurTransfer.Order13ActualPicardNormContinuousH1Exponent
#print axioms MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.pointsTopology
#print axioms MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.actualPiContinuousH1_killed_nineteen
#print axioms MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.actualPiConjugateContinuousH1_killed_nineteen


