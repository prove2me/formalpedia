-- Prove2me | Definitions.Def_OAIQ031A163
-- name    : OAIQ031A163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:13:05.98099+00:00
-- url     : https://prove2.me/theorems/7e7db57e-600e-4716-8f9c-549a4041688b
-- title:
--   Definitions bundle OAIQ031A163 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 29 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.T.BranchHom`, `OAI.ArExplicit.T.FiberHom`, `OAI.ArExplicit.T.SimpleHom`, `OAI.ArExplicit.T.betaTransferRaw`, `OAI.ArExplicit.T.bimoduleAugmentation`, `OAI.ArExplicit.T.branchTargetObject`, `OAI.ArExplicit.T.concreteNativeResolutionBaseModule`, `OAI.ArExplicit.T.evaluatedBaseZeroEquiv`, `OAI.ArExplicit.T.evaluatedFiber`, `OAI.ArExplicit.T.evaluatedFreeCoordinate`, `OAI.ArExplicit.T.evaluatedMiddle`, `OAI.ArExplicit.T.evaluatedSimpleObject`, `OAI.ArExplicit.T.evaluatedSingletonFst`, `OAI.ArExplicit.T.evaluatedSingletonModule`, `OAI.ArExplicit.T.evaluatedSingletonPairEquiv`, `OAI.ArExplicit.T.evaluatedSingletonProductIso`, `OAI.ArExplicit.T.evaluatedSingletonResolution`, `OAI.ArExplicit.T.evaluatedSingletonSnd`, `OAI.ArExplicit.T.evaluatedTwistPairEquiv`, `OAI.ArExplicit.T.finiteFiber`, `OAI.ArExplicit.T.freeCoordinateRaw`, `OAI.ArExplicit.T.middlePairResolutionIso`, `OAI.ArExplicit.T.middleSimpleStableIso`, `OAI.ArExplicit.T.middleToSimplePair`, `OAI.ArExplicit.T.nativeEvaluation`, `OAI.ArExplicit.T.simpleHomotopyObject`, `OAI.ArExplicit.T.simpleNativeTensorResolution`, `OAI.ArExplicit.T.simpleRegularEndpoint`, `OAI.ArExplicit.T.simpleResolutionTermIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_BranchHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/BranchHomCoordinates.lean), [`AuslanderReiten_Evaluation_ConcreteBaseAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteBaseAugmentation.lean), [`AuslanderReiten_Evaluation_ConcreteBetaTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteBetaTransfer.lean), [`AuslanderReiten_Evaluation_ConcreteNativeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteNativeAugmentation.lean), [`AuslanderReiten_Evaluation_EvaluatedBaseShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedBaseShift.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleShift.lean), [`AuslanderReiten_Fibers_ConcreteFiberEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberEvaluation.lean), [`AuslanderReiten_Fibers_ConcreteFiberHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberHomCoordinates.lean), [`AuslanderReiten_Fibers_ConcreteFiberHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberHomotopy.lean), [`AuslanderReiten_Fibers_ExplicitBimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ExplicitBimoduleFiber.lean), [`AuslanderReiten_Resolutions_ConcreteNativeResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteNativeResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A159` and `OAIQ031A160` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A168`, `OAIQ031A169`, `OAIQ031A170`, `OAIQ031A171`, `OAIQ031A172`, `OAIQ031A173` and `OAIQ031A174`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A159
import Definitions.Def_OAIQ031A160

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedBaseShift
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q

attribute [local instance] OAI.ArExplicit.T.baseScalar
attribute [local instance] OAI.ArExplicit.T.baseTower
def evaluatedBaseZeroEquiv : (evaluatedBaseModule q 0).carrier ≃ₗ[R] (X).carrier :=
  (EnvelopingBimodule.tensorCongr
    (M := (TwoCone.baseCokernelModule D hf 0).carrier)
    (N := AbsoluteBar.moduleObject k R 0) (bimoduleBaseCokernelEquiv q) (X).carrier).trans
      (BarBalanced.zeroEvaluationEquiv k R (X).carrier)

@[simp] theorem evaluatedBaseZeroEquiv_tmul
    (b : EnvelopingBimodule k R (TwoCone.baseCokernelModule D hf 0).carrier)
    (x : (X).carrier) :
    evaluatedBaseZeroEquiv q (BalancedTensor.tmul b x) =
      (show R from bimoduleBaseCokernelEquiv q b.value) • x := rfl

open scoped ModuleCat.Algebra

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedMiddleShift
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
abbrev evaluatedSimpleObject := (Q).obj ((X).completeCochain τ)

abbrev evaluatedSingletonModule (n : ℕ) := (X).evaluated (TwoCone.middleCokernelModule D hf n)

abbrev evaluatedSingletonResolution (n : ℕ) :=
  (Q).obj ((evaluatedSingletonModule q n).completeCochain τ)

def evaluatedSingletonPairEquiv (n : ℕ) : (evaluatedSingletonModule q n).carrier ≃ₗ[R]
    (FiniteLeftModule.pairModule (evaluatedBaseModule q (n+2))
      (evaluatedBaseModule q (n+2))).carrier :=
  FiniteLeftModule.evaluatedPairEquiv X (TwoCone.baseCokernelModule D hf (n+2))
    (TwoCone.baseCokernelModule D hf (n+2))

def evaluatedSingletonProductIso (n : ℕ) : evaluatedSingletonResolution q n ≅
    (evaluatedBaseResolution q (n+2) ⊞ evaluatedBaseResolution q (n+2)) :=
  (FiniteLeftModule.resolutionIso τ (evaluatedSingletonPairEquiv q n)).trans
    (FiniteLeftModule.resolutionPairIso τ (evaluatedBaseModule q (n+2))
      (evaluatedBaseModule q (n+2)))

def evaluatedSingletonFst (n : ℕ) : (evaluatedSingletonModule q n).carrier →ₗ[R]
    (evaluatedBaseModule q (n+2)).carrier :=
  (LinearMap.fst R _ _).comp (evaluatedSingletonPairEquiv q n).toLinearMap

def evaluatedSingletonSnd (n : ℕ) : (evaluatedSingletonModule q n).carrier →ₗ[R]
    (evaluatedBaseModule q (n+2)).carrier :=
  (LinearMap.snd R _ _).comp (evaluatedSingletonPairEquiv q n).toLinearMap

@[simp] theorem evaluatedSingletonProductIso_fst (n : ℕ) :
    (evaluatedSingletonProductIso q n).hom ≫ biprod.fst =
      (Q).map (FiniteLeftModule.resolutionMap τ (evaluatedSingletonFst q n)) := by
  simp only [evaluatedSingletonProductIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_fst, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ _ _).symm

@[simp] theorem evaluatedSingletonProductIso_snd (n : ℕ) :
    (evaluatedSingletonProductIso q n).hom ≫ biprod.snd =
      (Q).map (FiniteLeftModule.resolutionMap τ (evaluatedSingletonSnd q n)) := by
  simp only [evaluatedSingletonProductIso, Iso.trans_hom, Category.assoc,
    FiniteLeftModule.resolutionPairIso_hom_snd, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ _ _).symm

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ExplicitBimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "Ae" => R ⊗[k] Rᵐᵒᵖ

abbrev finiteFiber : FiniteLeftModule k Ae :=
  BimoduleFiber.finiteModule (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)
local notation "Y" => fiberTarget q

abbrev evaluatedFiber := FiniteLeftModule.evaluated X (finiteFiber q H₁ H₂)

abbrev evaluatedMiddle := FiniteLeftModule.evaluated X (FiniteLeftModule.fiberSource U₁ U₂ Y)

def evaluatedTwistPairEquiv :
    ((FiniteLeftModule.evaluated X U₁).carrier × (FiniteLeftModule.evaluated X U₂).carrier) ≃ₗ[R]
      ((X).carrier × (X).carrier) :=
  LinearEquiv.prodCongr (evaluatedTwistEquiv q H₁) (evaluatedTwistEquiv q H₂)

def middleToSimplePair : (evaluatedMiddle q H₁ H₂).carrier →ₗ[R] ((X).carrier × (X).carrier) :=
  (evaluatedTwistPairEquiv q H₁ H₂).toLinearMap.comp
    (FiniteLeftModule.middlePairMap X U₁ U₂ Y)

def middleSimpleStableIso : StableIsomorphism R (evaluatedMiddle q H₁ H₂).carrier
    ((X).carrier × (X).carrier) :=
  (FiniteLeftModule.evaluatedMiddleStableIso X U₁ U₂ Y).trans
    (StableIsomorphism.ofLinearEquiv (evaluatedTwistPairEquiv q H₁ H₂))

@[simp] theorem middleSimpleStableIso_hom : (middleSimpleStableIso q H₁ H₂).hom =
    StableHom.classOf R _ _ (middleToSimplePair q H₁ H₂) := by
  change StableHom.comp (StableHom.classOf R _ _ (evaluatedTwistPairEquiv q H₁ H₂).toLinearMap)
    (FiniteLeftModule.evaluatedMiddleStableIso X U₁ U₂ Y).hom = _
  rw [FiniteLeftModule.evaluatedMiddleStableIso_hom, StableHom.comp_classOf]
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_BranchHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

abbrev branchTargetObject :=
  (Q₀).obj ((FiniteLeftModule.evaluated X₀ (fiberTarget q)).completeCochain τ₀)

abbrev BranchHom (a : ℤ) := evaluatedSimpleObject q ⟶ (branchTargetObject q)⟦a⟧

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBaseAugmentation
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q

def bimoduleAugmentation : (D).term 0 ⟶ AbsoluteBar.moduleObject k A₀ 0 :=
  (ExternalTensor.envelopingFunctor k T₀ T₀).map ((tensorBarResolution q).π.f 0) ≫
    (barTensorZeroEquiv k T₀ T₀).toModuleIso.hom

theorem bimoduleBaseCokernelEquiv_mk (x : (D).term 0) :
    bimoduleBaseCokernelEquiv q (Submodule.Quotient.mk x) = (bimoduleAugmentation q).hom x := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteNativeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q

local instance instModuleCarrierTensorProductCanonicalTensorSimple_r1389e3_1 : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance instModuleCarrierEnvelopingAModuleObjectOfNatNat_r1389e3_1 : Module k (AbsoluteBar.moduleObject k A₀ 0) :=
  moduleCatBaseModule (k := k) (R := A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0)
abbrev nativeEvaluation := EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier

def simpleRegularEndpoint : (nativeEvaluation q).obj (AbsoluteBar.moduleObject k A₀ 0) ⟶
    canonicalTensorSimple q :=
  BarBalanced.endpointWithCoefficients k A₀ (X).carrier (canonicalTensorSimple q)
    (nativeToCanonicalSimple q)

local instance instIsScalarTowerTensorProductAMulOppositeCarrierEnvelopingModuleObjectOfNatNat_r1389e3_1 : IsScalarTower k (A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0) :=
  moduleCatBaseTower (k := k) (R := A₀ ⊗[k] A₀ᵐᵒᵖ) (AbsoluteBar.moduleObject k A₀ 0)
theorem simpleBaseAugmentation :
    (nativeEvaluation q).map (bimoduleAugmentation q) ≫ simpleRegularEndpoint q =
      (simpleOrdinaryResolution q).π.f 0 ≫
        (evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom := by
  let f : (D).term 0 ⟶ (TwoCone.baseCokernelModule D hf 0).carrier :=
    ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) (LinearMap.range ((D).d 0)).mkQ
  have hb : f ≫ (bimoduleBaseCokernelEquiv q).toModuleIso.hom = bimoduleAugmentation q := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact bimoduleBaseCokernelEquiv_mk q
  have h := BarBalanced.regularEvaluatedAugmentation k A₀ (X).carrier
    (canonicalTensorSimple q) ((D).term 0) (TwoCone.baseCokernelModule D hf 0).carrier
    (nativeToCanonicalSimple q) f (bimoduleBaseCokernelEquiv q) (bimoduleAugmentation q) hb
  change (nativeEvaluation q).map (bimoduleAugmentation q) ≫ simpleRegularEndpoint q =
    (TwoCone.evaluatedOrdinaryAugmentation D hf X).f 0 ≫ _
  rw [TwoCone.evaluatedOrdinaryAugmentation_zero]
  exact h

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteNativeResolution
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q
local instance concreteNativeResolutionBaseModule : Module k (canonicalTensorSimple q) :=
  moduleCatBaseModule (k := k) (R := A₀) (canonicalTensorSimple q)
local instance concreteNativeResolutionBaseTower : IsScalarTower k A₀ (canonicalTensorSimple q) :=
  moduleCatBaseTower (k := k) (R := A₀) (canonicalTensorSimple q)

def simpleNativeTensorResolution : ProjectiveResolution (canonicalTensorSimple q) :=
  ExternalTensor.projectiveResolution k T₀ T₀ (ModuleBar.nativeResolution k T₀ S)
    (ModuleBar.nativeResolution k T₀ S)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBetaTransfer
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct

universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

def evaluatedFreeCoordinate :
    (simpleOrdinaryResolution q).complex.X 0 ⟶ ModuleCat.of (A k q) (A k q) :=
  (simpleNativeBarIso q).hom.f 0 ≫ simpleBarFreeCoordinate q hq

def simpleResolutionTermIso (n : ℕ) : (simpleOrdinaryResolution q).complex.X n ≅
    TwoCone.evaluatedRawTerm (k := k) (R := A k q) (bimoduleTwoConeData q) (bimodule_term_finite_k q)
      (A.simpleFiniteModule q) n :=
  TwoCone.evaluatedResolutionTermIso (k := k) (R := A k q) (bimoduleTwoConeData q) (bimodule_term_finite_k q)
    (A.simpleFiniteModule q) (bimodule_exact q) (baseTail_right_projective q)
    (bimodule_term_projective q) n

def freeCoordinateRaw : TwoCone.evaluatedRawTerm (k := k) (R := A k q) (bimoduleTwoConeData q)
    (bimodule_term_finite_k q) (A.simpleFiniteModule q) 0 →ₗ[A k q] A k q :=
  (evaluatedFreeCoordinate q hq).hom.comp (simpleResolutionTermIso q 0).inv.hom

def betaTransferRaw : (evaluatedBaseModule q 1).carrier →ₗ[A k q] A k q :=
  (freeCoordinateRaw q hq).comp
    (TwoCone.evaluatedBaseInclusion (k := k) (R := A k q) (bimoduleTwoConeData q)
      (bimodule_term_finite_k q) (bimodule_exact q) (A.simpleFiniteModule q) 0)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberHomotopy
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

def middlePairResolutionIso :
    (Q).obj ((evaluatedMiddle q H₁ H₂).completeCochain τ) ≅
      (Q).obj ((FiniteLeftModule.pairModule X X).completeCochain τ) :=
  FiniteLeftModule.stableResolutionIso (M := evaluatedMiddle q H₁ H₂)
    (N := FiniteLeftModule.pairModule X X) τ (middleSimpleStableIso q H₁ H₂)

@[simp] theorem middlePairResolutionIso_hom : (middlePairResolutionIso q H₁ H₂).hom =
    (Q).map (FiniteLeftModule.resolutionMap (M := evaluatedMiddle q H₁ H₂)
      (N := FiniteLeftModule.pairModule X X) τ (middleToSimplePair q H₁ H₂)) :=
  FiniteLeftModule.stableResolutionIso_hom_of_class τ _ _ (middleSimpleStableIso_hom q H₁ H₂)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
abbrev simpleHomotopyObject := (Q).obj ((X).completeCochain τ)
local notation "SX" => simpleHomotopyObject q

abbrev SimpleHom (n : ℤ) := SX ⟶ (SX)⟦n⟧
abbrev FiberHom (n : ℤ) := SX ⟶ ((Q).obj ((evaluatedFiber q H₁ H₂).completeCochain τ))⟦n⟧

end ArExplicit.T

end

end OAI
end


