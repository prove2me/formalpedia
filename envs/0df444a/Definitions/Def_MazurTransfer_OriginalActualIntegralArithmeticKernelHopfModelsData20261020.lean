-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
-- name    : MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T06:39:31.46982+00:00
-- url     : https://prove2.me/theorems/b71b652c-715e-4250-adca-1e3d6f8202cd
-- title:
--   Original arithmetic integral norm-kernel Hopf model predicate
-- statement:
--   Retain the complete original predicate requiring a finite-free cocommutative Hopf algebra with its same integral point functor on every algebra, multiplication and all algebra-map naturality, and arithmetic labels into the previously fixed norm kernel preserving addition, the existing arithmetic Galois action and exact agreement with that point functor. Retain all six original scoped group, action and certificate providers. The complete original predicate type and whole value, all provider types and three whole provider values, and every original coefficient and arithmetic context are independently checked. Named downstream consumer: actual finite-flat selected arithmetic character quotients and Kummer local conditions at nineteen.
-- source:
--   MazurTheorem Order13ActualIntegralArithmeticKernelHopfModels by Vas and contributors; preserve the entire original integral point functor and previously fixed arithmetic kernel action, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite-free cocommutative integral Hopf models labelled
by the SAME FIXED arithmetic norm kernel, retaining the SAME integral point functor
and its all-algebra naturality, addition and the
PREVIOUSLY DEFINED arithmetic Galois action for every field automorphism.
Named downstream consumer: actual finite-flat selected character quotients
at nineteen and their Kummer local conditions. No splitting is assumed.
-/

noncomputable section
namespace MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralHopfArithmeticKernelLabels Order13ActualArithmeticKernelAdditiveAction
open Order13IntegralArithmeticNormKernelComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralArithmeticKernelHopfModels : GrpObj (Over.mk actualPicard.toBase) := actualGroup
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
local instance instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) := kernelAdditiveAction K φ

def HasArithmeticIntegralKernelHopfModel : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (LocalRing q) H)
    (_ : Module.Finite (LocalRing q) H) (_ : Module.Free (LocalRing q) H)
    (_ : Coalgebra.IsCocomm (LocalRing q) H),
    ∃ eAll : ∀ (T : Type) [CommRing T] [Algebra (LocalRing q) T],
        WithConv (H →ₐ[LocalRing q] T) ≃ kernelPoints (localLaw q hq)
          (integralNorm q hq φ) (Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) T))),
      (∀ (T : Type) [CommRing T] [Algebra (LocalRing q) T]
          (f g : WithConv (H →ₐ[LocalRing q] T)),
        (eAll T (f * g)).val = (localLaw q hq).mul _ (eAll T f).val (eAll T g).val) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra (LocalRing q) T]
          [CommRing T'] [Algebra (LocalRing q) T'] (g : T →ₐ[LocalRing q] T')
          (f : WithConv (H →ₐ[LocalRing q] T)),
        (eAll T' (.toConv (g.comp f.ofConv))).val.val =
          Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (eAll T f).val.val) ∧
    ∃ e : WithConv (H →ₐ[LocalRing q] K) ≃ Additive (Kernel K φ),
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)),
        (∀ x : H, g x = σ (f x)) → e g = σ • e f) ∧
      ∀ f, kernelPointEquiv q hq K φ ((e f).toMul) = eAll K f



local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralArithmeticKernelHopfModels : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralArithmeticKernelHopfModels : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom



local instance instFactPrimeOfNatNat_order13ActualIntegralArithmeticKernelHopfModels : Fact (Nat.Prime 19) := ⟨by norm_num⟩


end MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.HasArithmeticIntegralKernelHopfModel
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralArithmeticKernelHopfModels
#print axioms MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instFactPrimeOfNatNat_order13ActualIntegralArithmeticKernelHopfModels


