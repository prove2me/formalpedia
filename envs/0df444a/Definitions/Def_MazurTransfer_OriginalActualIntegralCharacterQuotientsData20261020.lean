-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualIntegralCharacterQuotientsData20261020
-- name    : MazurTransfer_OriginalActualIntegralCharacterQuotientsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T18:26:51.211902+00:00
-- url     : https://prove2.me/theorems/f067150d-b6f2-4235-a096-b0b3c91ab05c
-- title:
--   Original coherent integral quotients of the previously selected arithmetic character maps
-- statement:
--   Retain the complete original coherent quotient predicate: one same finite-free cocommutative source Hopf model carries the entire original integral point functor, multiplication, all algebra naturality, fixed arithmetic labels and exact point agreement, together with a genuine finite-flat quotient realizing the same selected intertwining map. Retain all thirteen original scoped group, module, arithmetic action and certificate providers. The original predicate type and whole value, provider types and five whole provider values, and the same chosen-map and coefficient contexts are independently checked. Named downstream consumer: actual nineteen character Kummer unit conditions and original integral norm torsor pushforwards.
-- source:
--   MazurTheorem Order13ActualIntegralCharacterQuotients by Vas and contributors; retain one same source model and the previously selected character maps and arithmetic labels, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Definitions.Def_MazurTransfer_OriginalIntegralRepresentationQuotientData20261020
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: integral finite-flat quotients for the PREVIOUSLY SELECTED
pi and conjugate-pi character maps, preserving a single source Hopf algebra,
its all-algebra integral points and its actual arithmetic kernel labels.
Named downstream consumer: actual nineteen character Kummer unit conditions.
-/

noncomputable section
namespace MazurTransfer.Order13ActualIntegralCharacterQuotients
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13IntegralArithmeticNormKernelComparison Order13ActualPicardNormKernelGaloisAction
open Order13ActualArithmeticKernelAdditiveAction Order13ActualNormKernelF19Representation
open Order13ActualNormKernelFiniteModule Order13IntegralRepresentationQuotient
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
local instance instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) := kernelAdditiveAction K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ)

/-- One source model carries the entire integral functor, the fixed arithmetic
kernel labels, and a quotient realizing precisely the previously chosen map. -/
def HasCoherentIntegralCharacterQuotient : Prop :=
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (LocalRing q) G)
    (_ : Module.Finite (LocalRing q) G) (_ : Module.Free (LocalRing q) G)
    (_ : Coalgebra.IsCocomm (LocalRing q) G),
    ∃ eAll : ∀ (T : Type) [CommRing T] [Algebra (LocalRing q) T],
        WithConv (G →ₐ[LocalRing q] T) ≃ kernelPoints (localLaw q hq)
          (integralNorm q hq φ) (Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) T))),
      (∀ (T : Type) [CommRing T] [Algebra (LocalRing q) T]
          (f g : WithConv (G →ₐ[LocalRing q] T)),
        (eAll T (f * g)).val = (localLaw q hq).mul _ (eAll T f).val (eAll T g).val) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra (LocalRing q) T]
          [CommRing T'] [Algebra (LocalRing q) T'] (g : T →ₐ[LocalRing q] T')
          (f : WithConv (G →ₐ[LocalRing q] T)),
        (eAll T' (.toConv (g.comp f.ofConv))).val.val =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (eAll T f).val.val) ∧
    ∃ e : WithConv (G →ₐ[LocalRing q] K) ≃ Additive (Kernel K φ),
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (G →ₐ[LocalRing q] K)),
        (∀ x : G, g x = σ (f x)) → e g = σ • e f) ∧
      (∀ f, kernelPointEquiv q hq K φ ((e f).toMul) = eAll K f) ∧
      HasQuotientOfModel q K φ ρ p G e



local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralCharacterQuotients : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralCharacterQuotients : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom
local instance instIsFiniteLeftSchemeSchemePi_order13ActualIntegralCharacterQuotients : IsFinite schemePi.left := MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
local instance instIsFiniteLeftSchemeSchemePiConjugate_order13ActualIntegralCharacterQuotients : IsFinite schemePiConjugate.left := MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateFiniteProvider20261018
local instance instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualIntegralCharacterQuotients : Fact (∀ z : Kernel K schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen K⟩
local instance instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualIntegralCharacterQuotients : Fact (∀ z : Kernel K schemePiConjugate, z ^ 19 = 1) := ⟨piConjugate_kernel_exponent_nineteen K⟩
open NineteenRootsGaloisRepresentation Order13ActualOrderedCharacterContinuousH1
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualIntegralCharacterQuotients : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)



local instance instFactPrimeOfNatNat_order13ActualIntegralCharacterQuotients : Fact (Nat.Prime 19) := ⟨by norm_num⟩


end MazurTransfer.Order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.HasCoherentIntegralCharacterQuotient
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePi_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactPrimeOfNatNat_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
#print axioms MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualIntegralCharacterQuotients


