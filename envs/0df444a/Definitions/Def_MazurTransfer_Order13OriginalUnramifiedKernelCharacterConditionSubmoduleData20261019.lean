-- Prove2me | Definitions.Def_MazurTransfer_Order13OriginalUnramifiedKernelCharacterConditionSubmoduleData20261019
-- name    : MazurTransfer_Order13OriginalUnramifiedKernelCharacterConditionSubmoduleData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T18:51:43.36008+00:00
-- url     : https://prove2.me/theorems/0616dddd-76ac-49b8-a4e5-2337b466af06
-- title:
--   Original actual unramified character-kernel condition submodule
-- statement:
--   Retain the original genuine kernel character maps and the same submodule defined by conjugation covariance and all valuation inertia conditions away from 13 and 19, including 2. Five complete constructor types and whole values, 28 scoped provider types and 13 whole provider values, nine structural proof-helper types and 473 shared context types with 196 whole values are checked against the original module. Named downstream consumer: the original actual unramified character-kernel embedding and pi norm quotient dimension bound.
-- source:
--   MazurTheorem Order13ActualUnramifiedKernelCharacterEmbedding by Vas and contributors; original actual kernel character maps and condition submodule, with per-file Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original genuine character-kernel maps and the submodule cut out by conjugation covariance and every original valuation inertia condition away from 13 and 19. Submodule field laws are structural construction evidence; the image condition and embedding proofs are separate results.
Named downstream consumer: the fixed arithmetic unramified character-kernel embedding and its actual pi norm quotient dimension bound.
-/
import Definitions.Def_MazurTransfer_Order13OriginalSelectedUnramifiedCharacterClassSubmodulesData20261019
import Definitions.Def_MazurTransfer_OriginalContinuousScalarKernelCharacterMapsData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: embed the ORIGINAL unramified reflected-character class
space in genuine continuous characters of its SAME character kernel,
with conjugation covariance and EVERY old valuation inertia condition.
No arithmetic finiteness or dimension bound is assumed here.
Named downstream consumer: arithmetic Selmer bounds for the ORIGINAL pi
norm quotient through the checked character-finrank-plus-one reduction.
-/

noncomputable section
namespace MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualUnramifiedKernelCharacterEmbedding : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualUnramifiedKernelCharacterEmbedding : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
open Order13ActualNormKernelF19Representation Order13ActualNormFixedKernelEquivalence
open Order13ActualNormKernelFiniteModule
local instance instFactPrimeOfNatNat_order13ActualUnramifiedKernelCharacterEmbedding : Fact (Nat.Prime 19) := ⟨by decide⟩

open Order13ActualPicardSchemeNineteenNorm Order13ActualNormKernelFiniteModule
local instance instIsFiniteLeftSchemeSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : IsFinite schemePi.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.1.1
local instance instIsFiniteLeftSchemeSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : IsFinite schemePiConjugate.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.2.1
local instance instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualUnramifiedKernelCharacterEmbedding : Fact (∀ z : Kernel K schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen K⟩
local instance instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualUnramifiedKernelCharacterEmbedding : Fact (∀ z : Kernel K schemePiConjugate, z ^ 19 = 1) := ⟨piConjugate_kernel_exponent_nineteen K⟩
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) (Additive (Kernel K schemePi)) := kernelZModModule K schemePi
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) (Additive (Kernel K schemePiConjugate)) := kernelZModModule K schemePiConjugate
local instance instFactNeRatOfNat_order13ActualUnramifiedKernelCharacterEmbedding : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩


local instance instFiniteSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : Finite (Kernel K schemePi) := kernel_finite K schemePi
local instance instFiniteSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : Finite (Kernel K schemePiConjugate) := kernel_finite K schemePiConjugate


variable [IsAlgClosed K]
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCrossPairing
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K


open Order13ActualNormKernelInvariantDimensions Order13ActualComplementaryCharacterExactSequence
open Order13ActualArithmeticCharacterExactSequence Order13ActualCyclotomicThirteenKernelCharacter

open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open RepresentationCharacterTwist
local instance instTopologicalSpacePoints_order13ActualUnramifiedKernelCharacterEmbedding : TopologicalSpace (Points K) := ⊥
local instance instDiscreteTopologyPoints_order13ActualUnramifiedKernelCharacterEmbedding : DiscreteTopology (Points K) := ⟨rfl⟩
local instance instMulActionAlgEquivRatPoints_order13ActualUnramifiedKernelCharacterEmbedding : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer K
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K schemePi) := kernelAction K schemePi
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K schemePiConjugate) :=
  kernelAction K schemePiConjugate
open OneDimensionalSelectedQuotientKernel
open Order13ActualOrderedCharacterContinuousH1
local instance instFiniteDimensionalZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualUnramifiedKernelCharacterEmbedding : FiniteDimensional (ZMod 19) (Additive (Roots K)) :=
  FiniteDimensional.of_finrank_pos (by rw [roots_finrank_one K]; decide)

variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

open Order13ActualSelectedCharacterExactSequences
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestrictionF19
local instance instModuleZModOfNatNatContinuousH1SchemePi_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) (ContinuousH1 K schemePi) := globalH1ZModModule K schemePi
local instance instModuleZModOfNatNatContinuousH1SchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) (ContinuousH1 K schemePiConjugate) := globalH1ZModModule K schemePiConjugate
local instance instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K schemePi) :=
  Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K schemePi
local instance instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K schemePiConjugate) :=
  Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K schemePiConjugate

open Order13ActualSelectedCharacterKummerKernel
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "Hχ" => ContinuousFirstCohomologyPresentation.H1 Γ (Coefficient (piLineRepresentation K z hz))
local notation "H₀" => ContinuousFirstCohomologyPresentation.H1 Γ (Coefficient (trivialLineRepresentation K))
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficientPiLineRepresentation_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) Hχ := coefficientH1ZModModule (piLineRepresentation K z hz)
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficientTrivialLineRepresentation_order13ActualUnramifiedKernelCharacterEmbedding : Module (ZMod 19) H₀ := coefficientH1ZModModule (trivialLineRepresentation K)

open Order13ActualSelectedCharacterUnramifiedKernelLifts
open ContinuousScalarKernelCharacters
local notation "χ" => piConjugateReflectedCharacter K z hz
local notation "Mχ" => Coefficient (piLineRepresentation K z hz)

abbrev KernelCharacters := Additive ((χ).ker →ₜ* Mχ)

abbrev kernelCharactersZModModule : Module (ZMod 19) (KernelCharacters K z hz) :=
  AddCommGroup.zmodModule (fun f => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply ContinuousMonoidHom.ext
    intro s
    rw [ContinuousMonoidHom.pow_apply]
    exact coefficient_exponent_nineteen _ _)
local instance instModuleZModOfNatNatKernelCharacters : Module (ZMod 19) (KernelCharacters K z hz) := kernelCharactersZModModule K z hz

def evaluation (s : (χ).ker) : KernelCharacters K z hz →ₗ[ZMod 19] ZMod 19 :=
  ({ toFun := fun f => (f.toMul s).val
     map_zero' := rfl
     map_add' := fun _ _ => rfl } : KernelCharacters K z hz →+ ZMod 19).toZModLinearMap 19

def piKernelCharacterMap : Hχ →ₗ[ZMod 19] KernelCharacters K z hz :=
  (kernelCharacters χ).toZModLinearMap 19



def piKernelCharacterConditions : Submodule (ZMod 19) (KernelCharacters K z hz) where
  carrier := {f | (∀ (g : Γ) (s : (χ).ker),
      evaluation K z hz (conjugateKernelElement χ g s) f = (χ g : ZMod 19) * evaluation K z hz s f) ∧
    ∀ (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
      (A : ValuationSubring K) (hA : A.LiesOverPrime q) (s : (χ).ker),
      s.val ∈ A.inertiaSubgroupIn ℚ → evaluation K z hz s f = 0}
  zero_mem' := by constructor <;> intros <;> simp only [map_zero, mul_zero]
  add_mem' := by
    intro f g hf hg
    constructor
    · intro a s
      rw [map_add, map_add, hf.1 a s, hg.1 a s, mul_add]
    · intro q hq h13 h19 A hA s hs
      rw [map_add, hf.2 q h13 h19 A hA s hs, hg.2 q h13 h19 A hA s hs, add_zero]
  smul_mem' := by
    intro a f hf
    constructor
    · intro g s
      rw [map_smul, map_smul, hf.1 g s]
      change a * ((χ g : ZMod 19) * _) = (χ g : ZMod 19) * (a * _)
      ring
    · intro q hq h13 h19 A hA s hs
      rw [map_smul, hf.2 q h13 h19 A hA s hs, smul_zero]







end MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding

end
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFactPrimeOfNatNat_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instIsFiniteLeftSchemeSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFactNeRatOfNat_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFiniteSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFiniteSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instTopologicalSpacePoints_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instDiscreteTopologyPoints_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instMulActionAlgEquivRatPoints_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instFiniteDimensionalZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatContinuousH1SchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatContinuousH1SchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatH1AlgEquivRatCoefficientPiLineRepresentation_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatH1AlgEquivRatCoefficientTrivialLineRepresentation_order13ActualUnramifiedKernelCharacterEmbedding
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.instModuleZModOfNatNatKernelCharacters
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.KernelCharacters
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.kernelCharactersZModModule
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.evaluation
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.piKernelCharacterMap
#print axioms MazurTransfer.Order13ActualUnramifiedKernelCharacterEmbedding.piKernelCharacterConditions


