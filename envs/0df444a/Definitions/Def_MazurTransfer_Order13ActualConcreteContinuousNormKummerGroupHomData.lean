-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualConcreteContinuousNormKummerGroupHomData
-- name    : MazurTransfer_Order13ActualConcreteContinuousNormKummerGroupHomData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T00:23:04.49999+00:00
-- url     : https://prove2.me/theorems/4d29a24d-df34-45d3-b64d-5ee041773883
-- title:
--   The two original concrete continuous actual norm Kummer group embeddings
-- statement:
--   For the same actual rational Picard P and its original norm maps pi and pi-bar, retain the original injective group homomorphisms $$P(\mathbb Q)/\varphi(P(\mathbb Q))\longrightarrow H^1_{\mathrm{cont}}(\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q}),\ker(\varphi)(\overline{\mathbb Q})),$$ for phi equal to either norm map. The target is written multiplicatively for the group homomorphisms. The constructors specialize the accepted generic continuous quotient map and its injectivity theorem. All four complete original types and both constructor values are compared, with complete relevant group/topology/action providers. The required finiteness facts come from the publicly proved actual norm finite-etale contract and are compared with the complete original proposition types. The named downstream consumer is the actual local Selmer condition and rational rank bound; those bounds remain separate.
-- source:
--   Original MazurTheorem Order13ActualPicardNormContinuousKummerInjection concrete continuous norm group maps and immediate injectivity wrappers, Apache-2.0. Explicit original point-action structure and public finite-proof projections retain the original nonproof constructor values; packaged wrapper facts receive no extra owned theorem credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational norm quotients inject by group
homomorphisms into continuous H1 of the actual geometric norm kernels.
The checked forgetful maps recover the prior algebraic Kummer maps.
Named downstream consumer: the local Selmer conditions and rank-zero bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormKummerEmbeddingsData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousKummerInjection_continuousQuotientHom_injective
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective

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
local instance actualConcreteContinuousNormKummerGroupHomDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualConcreteContinuousNormKummerGroupHomDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualConcreteContinuousNormKummerGroupHomDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualConcreteContinuousNormKummerGroupHomDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualConcreteContinuousNormKummerGroupHomDataProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualConcreteContinuousNormKummerGroupHomDataProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualConcreteContinuousNormKummerGroupHomDataProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualConcreteContinuousNormKummerGroupHomDataProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualConcreteContinuousNormKummerGroupHomDataProvider920261017 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ


variable (hsurj : Function.Surjective (normHom K φ))

local instance actualConcreteContinuousNormKummerGroupHomDataProvider1020261017 : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
local instance actualConcreteContinuousNormKummerGroupHomDataProvider1120261017 : IsFinite schemePi.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance actualConcreteContinuousNormKummerGroupHomDataProvider1220261017 : IsFinite schemePiConjugate.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1

def actualPiAlgebraicClosureContinuousKummerGroupHom :
    NormQuotient schemePi →* Multiplicative (ContinuousH1 (AlgebraicClosure ℚ) schemePi) :=
  continuousQuotientHom (AlgebraicClosure ℚ) schemePi
    (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ))

theorem actualPiAlgebraicClosureContinuousKummerGroupHom_injective :
    Function.Injective actualPiAlgebraicClosureContinuousKummerGroupHom :=
  continuousQuotientHom_injective (AlgebraicClosure ℚ) schemePi
    (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ))

def actualPiConjugateAlgebraicClosureContinuousKummerGroupHom :
    NormQuotient schemePiConjugate →*
      Multiplicative (ContinuousH1 (AlgebraicClosure ℚ) schemePiConjugate) :=
  continuousQuotientHom (AlgebraicClosure ℚ) schemePiConjugate
    (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ))

theorem actualPiConjugateAlgebraicClosureContinuousKummerGroupHom_injective :
    Function.Injective actualPiConjugateAlgebraicClosureContinuousKummerGroupHom :=
  continuousQuotientHom_injective (AlgebraicClosure ℚ) schemePiConjugate
    (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ))

end MazurTransfer.Order13ActualPicardNormContinuousKummerInjection
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.actualPiAlgebraicClosureContinuousKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.actualPiAlgebraicClosureContinuousKummerGroupHom_injective
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.actualPiConjugateAlgebraicClosureContinuousKummerGroupHom
#print axioms MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.actualPiConjugateAlgebraicClosureContinuousKummerGroupHom_injective


