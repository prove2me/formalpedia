-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualPiMu19CoherentQuotientData20261020
-- name    : MazurTransfer_OriginalActualPiMu19CoherentQuotientData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-11-02T16:47:31.758498+00:00
-- url     : https://prove2.me/theorems/d87e411b-6190-4c89-960f-abec19283723
-- title:
--   Original coherent actual pi kernel point equivalence and normalized mu19 model predicate
-- statement:
--   Retain the same integral kernel Hopf model, its full point functor over every coefficient algebra, multiplication, every algebra map and the original arithmetic kernel label. The checked actual nineteen selected character quotients provide that model and its selected pi quotient. Apply the checked same-model normalized literal mu19 quotient theorem to that exact quotient, retaining every chosen map and restriction identity. The complete original proposition and helper type, both original constructor full types and whole values, fourteen scoped provider types and six whole values, every generated helper type and all original selected-map contexts are independently checked. Named downstream consumer: the actual integral pi norm-preimage torsors and their literal mu19 cocycle pushforward.
-- source:
--   MazurTheorem Order13ActualPiMu19CoherentQuotient by Vas and contributors; same selected pi quotient and normalized literal mu19 model, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalSelectedPiMu19QuotientData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the SAME selected piQuotient model in NORMALIZED literal mu19 coordinates, bialgebra
inclusion, arithmetic label and restriction identity when classifying
its canonical scalar base change at nineteen. No replacement quotient.
Named downstream consumer: pushforward of the actual integral pi torsor
and its literal-mu19 Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.Order13ActualPiMu19CoherentQuotient
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SameIntegralPicardRationalSchemeComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13IntegralRepresentationQuotient Order13ActualOrderedCharacterContinuousH1
open Order13RationalSubringBaseChange NineteenRootsGaloisRepresentation
open Order13RationalSubringMu19Classification CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open BialgebraBaseChangePointRestriction
open Order13SelectedPiMu19Quotient Order13ActualIntegralCharacterQuotients
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open RelativeGroupLawFiniteFlatKernelHopf Order13IntegralArithmeticNormKernelComparison
open Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
local instance instIsGaloisRatAlgebraicClosure_order13ActualPiMu19CoherentQuotient : IsGalois ℚ F := Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
local instance instFactPrimeOfNatNat_order13ActualPiMu19CoherentQuotient : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13ActualPiMu19CoherentQuotient : Algebra R F := Algebra.compHom F (algebraMap R ℚ)
local instance instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13ActualPiMu19CoherentQuotient : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
local instance instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13ActualPiMu19CoherentQuotient : IsScalarTower R S F :=
  localSubringTower 19 F (aRK := (inferInstance : Algebra R F))
    (tRQ := (inferInstance : IsScalarTower R ℚ F))
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualPiMu19CoherentQuotient : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualPiMu19CoherentQuotient : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualPiMu19CoherentQuotient : IsMonHom schemePi := schemePi_isMonHom
local instance instIsFiniteLeftSchemeSchemePi_order13ActualPiMu19CoherentQuotient : IsFinite schemePi.left := MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
local instance instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13ActualPiMu19CoherentQuotient : Fact (∀ z : Kernel F schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen F⟩
local instance instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient : Module (ZMod 19) (Additive (Kernel F schemePi)) := kernelZModModule F schemePi
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13ActualPiMu19CoherentQuotient : Module (ZMod 19) (Additive (Roots F)) := rootsZModModule F

variable (z : F) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
local instance instMulDistribMulActionAlgEquivRatAlgebraicClosureSubtypePointsMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient : MulDistribMulAction (F ≃ₐ[ℚ] F) (Kernel F schemePi) := kernelAction F schemePi
local instance instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient : DistribMulAction (F ≃ₐ[ℚ] F) (Additive (Kernel F schemePi)) := kernelAdditiveAction F schemePi

def fixedKernelPointEquiv :=
  @Order13IntegralArithmeticNormKernelComparison.kernelPointEquiv 19 inferInstance
    Order13ExceptionalNineteenFlatNormFibres.nineteen_good F _ _
    (inferInstance : Algebra R F) (inferInstance : IsScalarTower R ℚ F) schemePi inferInstance

def HasCoherentActualPiMu19Model : Prop :=
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (LocalRing 19) G)
    (_ : Module.Finite (LocalRing 19) G) (_ : Module.Free (LocalRing 19) G)
    (_ : Coalgebra.IsCocomm (LocalRing 19) G),
    ∃ eAll : ∀ (T : Type) [CommRing T] [Algebra (LocalRing 19) T],
        WithConv (G →ₐ[LocalRing 19] T) ≃ kernelPoints (localLaw 19 Order13ExceptionalNineteenFlatNormFibres.nineteen_good)
          (integralNorm 19 Order13ExceptionalNineteenFlatNormFibres.nineteen_good schemePi) (Spec.map (CommRingCat.ofHom (algebraMap (LocalRing 19) T))),
      (∀ (T : Type) [CommRing T] [Algebra (LocalRing 19) T]
          (f g : WithConv (G →ₐ[LocalRing 19] T)),
        (eAll T (f * g)).val = (localLaw 19 Order13ExceptionalNineteenFlatNormFibres.nineteen_good).mul _ (eAll T f).val (eAll T g).val) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra (LocalRing 19) T]
          [CommRing T'] [Algebra (LocalRing 19) T'] (g : T →ₐ[LocalRing 19] T')
          (f : WithConv (G →ₐ[LocalRing 19] T)),
        (eAll T' (.toConv (g.comp f.ofConv))).val.val =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (eAll T f).val.val) ∧
    ∃ e : WithConv (G →ₐ[LocalRing 19] F) ≃ Additive (Kernel F schemePi),
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (G →ₐ[LocalRing 19] F)),
        (∀ x : G, g x = σ (f x)) → e g = σ • e f) ∧
      (∀ f, fixedKernelPointEquiv ((e f).toMul) = eAll F f) ∧
      HasSelectedNormalizedMu19Quotient z hz 𝒱 G e




end MazurTransfer.Order13ActualPiMu19CoherentQuotient

#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.fixedKernelPointEquiv
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.HasCoherentActualPiMu19Model
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instFactPrimeOfNatNat_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsFiniteLeftSchemeSchemePi_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsGaloisRatAlgebraicClosure_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instFactForallEqSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePiHPowOfNat_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instModuleZModOfNatNatAdditiveSubtypePointsAlgebraicClosureRatMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualPiMu19CoherentQuotient
#print axioms MazurTransfer.Order13ActualPiMu19CoherentQuotient.instMulDistribMulActionAlgEquivRatAlgebraicClosureSubtypePointsMemSubgroupKernelSchemePi_order13ActualPiMu19CoherentQuotient


