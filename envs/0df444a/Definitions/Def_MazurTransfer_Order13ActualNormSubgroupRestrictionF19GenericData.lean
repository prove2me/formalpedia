-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19GenericData
-- name    : MazurTransfer_Order13ActualNormSubgroupRestrictionF19GenericData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:10:41.266537+00:00
-- url     : https://prove2.me/theorems/7ff60fa1-1ea2-466d-bf1e-113e3ccb620e
-- title:
--   Original F19-linear restriction map and subgroup-invariant norm-preimage subspace
-- statement:
--   For a characteristic-zero Galois extension K of Q, a finite internal group endomorphism phi of the same actual rational Picard, an arbitrary subgroup S of Aut_Q(K), and the original exponent-nineteen kernel fact, retain the original global and restricted H1 modules over ZMod 19, the linear restriction map, and its kernel. The kernel contains a norm class exactly when that norm has an S-invariant preimage. The inherited Krull subgroup topology and original discrete coefficients are retained. All seven original declaration types, five nonproof constructor values, and both original module instance providers are compared in full, along with group/topology/action dependencies. The named downstream consumer is the actual inertia local condition; identification with arithmetic inertia and inclusion of the global Kummer image remain separate.
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
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousH1Exponent_continuousH1_killed_nineteen
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestrictionF19_restrictedH1_killed_nineteen
import Mathlib.Algebra.Module.ZMod

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
local instance actualNormSubgroupF19GenericDataProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormSubgroupF19GenericDataProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormSubgroupF19GenericDataProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormSubgroupF19GenericDataProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualNormSubgroupF19GenericDataProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormSubgroupF19GenericDataProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormSubgroupF19GenericDataProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormSubgroupF19GenericDataProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance actualNormSubgroupF19GenericDataProvider920261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ


open Order13ActualPicardNormContinuousCohomology
variable (S : Subgroup (K ≃ₐ[ℚ] K))


open Order13ActualPicardNormSubgroupRestriction

theorem subgroup_kernelContinuousSMul : ContinuousSMul S (Kernel K φ) := by
  refine ⟨?_⟩
  change Continuous (fun p : S × Kernel K φ => p.1.val • p.2)
  exact continuous_smul.comp (continuous_subtype_val.prodMap continuous_id)

variable [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
abbrev globalH1ZModModule : Module (ZMod 19) (ContinuousH1 K φ) :=
  AddCommGroup.zmodModule (MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.continuousH1_killed_nineteen K φ Fact.out)
abbrev restrictedH1ZModModule : Module (ZMod 19) (localContinuousH1 K φ S) :=
  AddCommGroup.zmodModule (restrictedH1_killed_nineteen K φ S Fact.out)
local instance actualNormSubgroupF19GenericDataProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormSubgroupF19GenericDataProvider1120261018 : Module (ZMod 19) (localContinuousH1 K φ S) := restrictedH1ZModModule K φ S

def restrictionLinearMap : ContinuousH1 K φ →ₗ[ZMod 19] localContinuousH1 K φ S :=
  (restrictNormClass K φ S).toZModLinearMap 19

def subgroupTrivialClasses : Submodule (ZMod 19) (ContinuousH1 K φ) :=
  (restrictionLinearMap K φ S).ker

theorem class_mem_subgroupTrivialClasses_iff_invariant_preimage
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    continuousClassOfLift K φ a b hb ∈ subgroupTrivialClasses K φ S ↔
      ∃ c : Points K, c ≫ φ = rationalPoint K a ∧ ∀ σ : S, actionHom K σ.val c = c :=
  restrictedClass_zero_iff_subgroup_invariant_preimage K φ S a b hb

end MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.pointsTopology
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.subgroup_kernelContinuousSMul
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.globalH1ZModModule
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.restrictedH1ZModModule
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.subgroupTrivialClasses
#print axioms MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.class_mem_subgroupTrivialClasses_iff_invariant_preimage


