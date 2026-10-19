-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLiftsOriginalData20261019
-- name    : MazurTransfer_Order13ActualCharacterGoodPrimeKernelLiftsOriginalData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T01:28:04.639907+00:00
-- url     : https://prove2.me/theorems/cb03dada-c237-4077-bb88-d2a026afa660
-- title:
--   Original good-prime character Kummer class predicates
-- statement:
--   The original character cohomology classes vanishing on genuine valuation inertia at every prime outside two, thirteen and nineteen, together with the actual character Kummer kernel-lift predicate. The three original constructor types and complete values, fourteen original instance types and nine instance values, and required contexts have been compared with the source. Named downstream consumer: actual good-prime character Kummer kernel control.
-- source:
--   MazurTheorem Order13ActualCharacterGoodPrimeKernelLifts, original pointsTopology, goodPrimeClasses and HasGoodPrimeCharacterKummerSequence; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual character-line lifts of norm Kummer classes are
unramified on every genuine good-prime valuation inertia subgroup.
Named downstream consumer: character Selmer bounds for the actual norm images.
-/

import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
import Definitions.Def_FLTPrelim_Ramification

noncomputable section
namespace MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider120261019 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider220261019 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider320261019 : IsMonHom schemePi := schemePi_isMonHom
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider420261019 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider520261019 : TopologicalSpace (Points K) := pointsTopology K
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider620261019 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider720261019 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider820261019 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider920261019 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider1020261019 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider1120261019 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider1220261019 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider1320261019 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
local instance actualCharacterGoodPrimeKernelLiftsOriginalProvider1420261019 (S : Subgroup (K ≃ₐ[ℚ] K)) : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 S (Coefficient σ)) :=
  restrictedCoefficientH1ZModModule σ S

variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include hq hne hφ hA

omit hq hne hφ hA in
 def goodPrimeClasses : Submodule (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) where
  carrier := {y | ∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q),
      coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0}
  zero_mem' := by intro q hq hgood hne A hA; exact map_zero _
  add_mem' := by intro x y hx hy q hq hgood hne A hA; rw [map_add, hx q hgood hne A hA, hy q hgood hne A hA, add_zero]
  smul_mem' := by intro c x hx q hq hgood hne A hA; rw [map_smul, hx q hgood hne A hA, smul_zero]

omit hq hne hφ hA in
 def HasGoodPrimeCharacterKummerSequence (hsurj : Function.Surjective (normHom K φ)) : Prop :=
  ∃ i : Representation.IntertwiningMap σ (kernelRepresentation K φ),
  ∃ p : Representation.IntertwiningMap (kernelRepresentation K φ) τ,
    Function.Injective i ∧ Function.Surjective p ∧
    LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap ∧
    LinearMap.range (inclusionClass K φ σ i) = LinearMap.ker (mapClass K φ τ p) ∧
    ∀ x : NormQuotient φ, normQuotientCharacterHom K φ τ p hsurj x = 1 →
      ∃ y ∈ goodPrimeClasses K σ,
        inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd

end MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts
#print axioms MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.pointsTopology
#print axioms MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.goodPrimeClasses
#print axioms MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.HasGoodPrimeCharacterKummerSequence


