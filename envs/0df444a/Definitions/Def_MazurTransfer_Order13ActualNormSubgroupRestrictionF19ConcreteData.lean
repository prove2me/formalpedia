-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19ConcreteData
-- name    : MazurTransfer_Order13ActualNormSubgroupRestrictionF19ConcreteData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:13:14.13551+00:00
-- url     : https://prove2.me/theorems/f3dbbd7c-b0fc-410c-9bd9-ab1ff4f7345f
-- title:
--   Original F19-linear subgroup restriction maps for the two actual norm factors
-- statement:
--   For the two original norm maps of the same actual rational Picard over the algebraic closure of Q, retain their original F19-linear continuous H1 restriction maps for every subgroup S of the absolute rational Galois group. Both complete original types and both nonproof constructor values are compared, including both original module instance providers and all relevant group/topology/action providers. Finite-map proofs come from the accepted finite-etale norm contract and have the same complete original proposition types. The named downstream consumer is the original local norm Selmer conditions. No arithmetic identification of S, finiteness or dimension bound is asserted.
-- source:
--   Original MazurTheorem Order13ActualPicardNormSubgroupRestrictionF19, Apache-2.0. Original constructors and immediate specialization/computation facts retain their full original types. Packaged proof-valued facts receive no extra owned theorem credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm class restrictions are F19-linear. Their
kernels are the subspaces with subgroup-invariant norm preimages.
Named downstream consumer: unramified conditions at actual inertia groups.
No identification of inertia groups or inclusion of global Kummer images
in these subspaces is asserted by this interface.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19GenericData
import Definitions.Def_MazurTransfer_Order13ActualSpecificContinuousNormH1ExponentData

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormSubgroupF19ConcreteDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormSubgroupF19ConcreteDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormSubgroupF19ConcreteDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormSubgroupF19ConcreteDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormSubgroupF19ConcreteDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormSubgroupF19ConcreteDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormSubgroupF19ConcreteDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormSubgroupF19ConcreteDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormSubgroupF19ConcreteDataProvider920261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ


open Order13ActualPicardNormContinuousCohomology
variable (S : Subgroup (K ≃ₐ[ℚ] K))


open Order13ActualPicardNormSubgroupRestriction

variable [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormSubgroupF19ConcreteGlobalModuleProvider20261018 :
    Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormSubgroupF19ConcreteRestrictedModuleProvider20261018 :
    Module (ZMod 19) (localContinuousH1 K φ S) := restrictedH1ZModModule K φ S

local instance actualNormSubgroupF19ConcreteSpecificProvider120261018 : IsGalois ℚ (AlgebraicClosure ℚ) :=
  Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
local instance actualNormSubgroupF19ConcreteSpecificProvider220261018 : IsFinite schemePi.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance actualNormSubgroupF19ConcreteSpecificProvider320261018 : IsFinite schemePiConjugate.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1
local instance actualNormSubgroupF19ConcreteSpecificProvider420261018 : Fact (∀ z : Kernel (AlgebraicClosure ℚ) schemePi, z ^ 19 = 1) :=
  ⟨pi_kernel_exponent_nineteen (AlgebraicClosure ℚ)⟩
local instance actualNormSubgroupF19ConcreteSpecificProvider520261018 : Fact (∀ z : Kernel (AlgebraicClosure ℚ) schemePiConjugate, z ^ 19 = 1) :=
  ⟨piConjugate_kernel_exponent_nineteen (AlgebraicClosure ℚ)⟩

def actualPiRestrictionLinearMap (S' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ContinuousH1 (AlgebraicClosure ℚ) schemePi →ₗ[ZMod 19]
      localContinuousH1 (AlgebraicClosure ℚ) schemePi S' :=
  restrictionLinearMap (AlgebraicClosure ℚ) schemePi S'

def actualPiConjugateRestrictionLinearMap
    (S' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ContinuousH1 (AlgebraicClosure ℚ) schemePiConjugate →ₗ[ZMod 19]
      localContinuousH1 (AlgebraicClosure ℚ) schemePiConjugate S' :=
  restrictionLinearMap (AlgebraicClosure ℚ) schemePiConjugate S'

end MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.actualPiRestrictionLinearMap
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.actualPiConjugateRestrictionLinearMap


