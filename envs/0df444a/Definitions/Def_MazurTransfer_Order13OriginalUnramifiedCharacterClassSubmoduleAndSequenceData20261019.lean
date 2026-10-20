-- Prove2me | Definitions.Def_MazurTransfer_Order13OriginalUnramifiedCharacterClassSubmoduleAndSequenceData20261019
-- name    : MazurTransfer_Order13OriginalUnramifiedCharacterClassSubmoduleAndSequenceData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T12:45:35.752302+00:00
-- url     : https://prove2.me/theorems/e128b969-6531-404e-9cb8-3df74ba5bfc8
-- title:
--   Original unramified character-class submodule and exact sequence predicate
-- statement:
--   The original character cohomology submodule imposes zero restriction on every genuine valuation inertia subgroup at every prime other than 13 and 19, including 2. Preserve the same topology, kernel actions, cohomology modules and exact-sequence predicate. Whole submodule and predicate values and their generated structural proof helpers are checked against the originals. Named downstream consumer: original unramified character kernel lifts and actual selected-character Selmer bounds.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original character cohomology submodules impose zero restriction on EVERY genuine valuation inertia group away from 13 and 19, including 2; retain the same selected coefficient labels and maps. Submodule field laws are structural constructor evidence.
Named downstream consumer: original unramified character kernel-lift theorems and actual Selmer dimension bounds.
-/
import Definitions.Def_MazurTransfer_Order13OriginalCharacterLocalConditionScopedTopologyAndModuleData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual character-line lifts of norm Kummer classes are
unramified on every genuine valuation inertia subgroup away from thirteen and nineteen.
The dyadic case and all odd good primes use the SAME fixed norm kernels
and the original exact cohomology maps. No splitting is assumed.
Named downstream consumer: character Selmer bounds for the actual norm images.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualCharacterKernelLiftsAwayThirteenNineteen : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualCharacterKernelLiftsAwayThirteenNineteen : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance instTopologicalSpacePoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen : TopologicalSpace (Points K) := pointsTopology K
local instance instDiscreteTopologyPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen : DiscreteTopology (Points K) := ⟨rfl⟩
local instance instMulActionAlgEquivRatPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer K
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance instModuleZModOfNatNatContinuousH1_order13ActualCharacterKernelLiftsAwayThirteenNineteen : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen_1 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
local instance instModuleZModOfNatNatH1SubtypeAlgEquivRatMemSubgroupCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen (S : Subgroup (K ≃ₐ[ℚ] K)) : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 S (Coefficient σ)) :=
  restrictedCoefficientH1ZModModule σ S

variable (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include h13 h19 hφ hA





omit h13 h19 hφ hA in
 def unramifiedClassesAwayThirteenNineteen : Submodule (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) where
  carrier := {y | ∀ (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q),
      coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0}
  zero_mem' := by intro q h13 hgood h19 A hA; exact map_zero _
  add_mem' := by intro x y hx hy q h13 hgood h19 A hA; rw [map_add, hx q hgood h19 A hA, hy q hgood h19 A hA, add_zero]
  smul_mem' := by intro c x hx q h13 hgood h19 A hA; rw [map_smul, hx q hgood h19 A hA, smul_zero]



omit h13 h19 hφ hA in
 def HasUnramifiedAwayThirteenNineteenCharacterKummerSequence (hsurj : Function.Surjective (normHom K φ)) : Prop :=
  ∃ i : Representation.IntertwiningMap σ (kernelRepresentation K φ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K φ) τ,
    Function.Injective i ∧ Function.Surjective p ∧
    LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap ∧
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) ∧
    ∀ x : NormQuotient φ, normQuotientCharacterHom K φ τ p hsurj x = 1 →
      ∃ y ∈ unramifiedClassesAwayThirteenNineteen K σ,
        inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd



end MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen

end
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatContinuousH1_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen_1
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1SubtypeAlgEquivRatMemSubgroupCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.pointsTopology
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.unramifiedClassesAwayThirteenNineteen
#print axioms MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.HasUnramifiedAwayThirteenNineteenCharacterKummerSequence


