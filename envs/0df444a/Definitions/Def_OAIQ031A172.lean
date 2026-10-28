-- Prove2me | Definitions.Def_OAIQ031A172
-- name    : OAIQ031A172
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:32:42.345557+00:00
-- url     : https://prove2.me/theorems/3d3c56ea-f78f-4fa7-8568-d506f7e5a6ee
-- title:
--   Definitions bundle OAIQ031A172 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 17 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.T.evaluatedFiberSecond`, `OAI.ArExplicit.T.evaluatedMiddleInl`, `OAI.ArExplicit.T.evaluatedMiddleInr`, `OAI.ArExplicit.T.evaluatedRho₁`, `OAI.ArExplicit.T.evaluatedRho₂`, `OAI.ArExplicit.T.explicitAlgebra`, `OAI.ArExplicit.T.fiberHomRhoPair`, `OAI.ArExplicit.T.middleProductResolutionIso`, `OAI.ArExplicit.T.rho₁`, `OAI.ArExplicit.T.rho₂`, `OAI.ArExplicit.T.simpleFullHomEquiv`, `OAI.ArExplicit.T.simpleZeroScalarEquiv`, `OAI.ArExplicit.T.simpleZeroUnit`, `OAI.ArExplicit.T.tensorFiberComplete`, `OAI.ArExplicit.T.tensorFiberOut`, `OAI.ArExplicit.T.tensorRho₁`, `OAI.ArExplicit.T.tensorRho₂`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleHomScalars`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleHomScalars.lean), [`AuslanderReiten_Coordinates_ConcreteMainCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteMainCriterion.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiber.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiberProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiberProjection.lean), [`AuslanderReiten_Ext_ATwistedTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ATwistedTensorExt.lean), [`AuslanderReiten_Fibers_ConcreteFiberComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberComponents.lean), [`AuslanderReiten_Fibers_ConcreteFiberEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberEvaluation.lean), [`AuslanderReiten_Fibers_ConcreteFiberHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberHomCoordinates.lean), [`AuslanderReiten_Fibers_ConcreteFiberHomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberHomotopy.lean), [`AuslanderReiten_Fibers_ExplicitBimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ExplicitBimoduleFiber.lean), [`AuslanderReiten_Fibers_FiberFullHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberFullHomCoordinates.lean), [`AuslanderReiten_Modules_ATwistedCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ATwistedCompleteAction.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A163`, `OAIQ031A165`, `OAIQ031A166` and `OAIQ031A167` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A178` and `OAIQ031A179`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A163
import Definitions.Def_OAIQ031A165
import Definitions.Def_OAIQ031A166
import Definitions.Def_OAIQ031A167

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ExplicitBimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def rho₁ : (finiteFiber q H₁ H₂).carrier ⟶ (twistedFiniteModule (sourceTwist q H₁)).carrier :=
  FiniteLeftModule.fiberProjection₁
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

def rho₂ : (finiteFiber q H₁ H₂).carrier ⟶ (twistedFiniteModule (sourceTwist q H₂)).carrier :=
  FiniteLeftModule.fiberProjection₂
    (twistedFiniteModule (sourceTwist q H₁)) (twistedFiniteModule (sourceTwist q H₂))
    (fiberTarget q) (normalizedLift q H₁) (normalizedLift q H₂)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def evaluatedRho₁ : (evaluatedFiber q H₁ H₂).carrier →ₗ[R] (X).carrier :=
  (evaluatedTwistEquiv q H₁).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X (rho₁ q H₁ H₂).hom)

def evaluatedRho₂ : (evaluatedFiber q H₁ H₂).carrier →ₗ[R] (X).carrier :=
  (evaluatedTwistEquiv q H₂).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X (rho₂ q H₁ H₂).hom)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberHomotopy
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def middleProductResolutionIso :
    (Q).obj ((evaluatedMiddle q H₁ H₂).completeCochain τ) ≅
      ((Q).obj ((X).completeCochain τ) ⊞ (Q).obj ((X).completeCochain τ)) :=
  (middlePairResolutionIso q H₁ H₂).trans (FiniteLeftModule.resolutionPairIso τ X X)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "SX" => simpleHomotopyObject q

def fiberHomRhoPair (n : ℤ) : FiberHom q H₁ H₂ n →ₗ[k]
    (SimpleHom q n × SimpleHom q n) :=
  (Linear.rightComp k SX ((CategoryTheory.shiftFunctor HC n).map
    ((Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₁ q H₁ H₂))))).prod
    (Linear.rightComp k SX ((CategoryTheory.shiftFunctor HC n).map
      ((Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
        (N := X) τ (evaluatedRho₂ q H₁ H₂)))))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberFullHomCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "P₀" => A.simpleComplete q

def simpleFullHomEquiv (n : ℤ) : CohomologyClass P₀ P₀ n ≃ₗ[k] SimpleHom q n :=
  fullHomShiftedHomotopyEquiv k P₀ P₀ n

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleHomScalars
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)

def simpleZeroScalarEquiv (hq1 : 1+q ≠ 0) : SimpleHom q 0 ≃ₗ[k] k :=
  (simpleFullHomEquiv q 0).symm.trans (A.fullHomZeroScalarEquiv q hq1)

def simpleZeroUnit : SimpleHom q 0 :=
  (shiftFunctorZero HC ℤ).inv.app (simpleHomotopyObject q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiber
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance instFiniteAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber : Module.Finite (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_left q H₁ H₂).1
local instance instProjectiveAEnvelopingBimoduleCarrierTensorProductMulOppositeFiniteFiber : Module.Projective (A k q)
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_left q H₁ H₂).2
local instance instFiniteMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber : Module.Finite (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_right q H₁ H₂).1
local instance instProjectiveMulOppositeAEnvelopingBimoduleCarrierTensorProductFiniteFiber : Module.Projective (A k q)ᵐᵒᵖ
    (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier) :=
  by
    simpa only [explicitBimodule, BimoduleFiber.bimodule, BimoduleFiber.finiteModule, finiteFiber]
      using (explicitBimodule_right q H₁ H₂).2

abbrev tensorFiberComplete := BalancedTensor.completeTensor
  (F := EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)
    (AFrobeniusTrace k q) (A.simpleFiniteModule q)

abbrev tensorFiberOut := FiniteLeftModule.evaluatedResolutionOut
  (AFrobeniusTrace k q) (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)

theorem tensorFiberOut_rho₁ :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
        (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q) ≫
          BalancedTensor.comparisonOut (AFrobeniusTrace k q) (A.simpleFiniteModule q)
            (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)) =
    (HomotopyCategory.quotient _ _).map
      (tensorFiberOut q H₁ H₂ ≫
        FiniteLeftModule.resolutionMap (AFrobeniusTrace k q) (evaluatedRho₁ q H₁ H₂)) :=
  FiniteLeftModule.evaluatedResolutionOut_natural (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)
    (twistedFiniteModule (sourceTwist q H₁)) (rho₁ q H₁ H₂)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)

theorem tensorFiberOut_rho₂ :
    (HomotopyCategory.quotient _ _).map
      (BalancedTensor.complexMap (k := k) (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
        (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q) ≫
          BalancedTensor.comparisonOut (AFrobeniusTrace k q) (A.simpleFiniteModule q)
            (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)) =
    (HomotopyCategory.quotient _ _).map
      (tensorFiberOut q H₁ H₂ ≫
        FiniteLeftModule.resolutionMap (AFrobeniusTrace k q) (evaluatedRho₂ q H₁ H₂)) :=
  FiniteLeftModule.evaluatedResolutionOut_natural (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (finiteFiber q H₁ H₂)
    (twistedFiniteModule (sourceTwist q H₂)) (rho₂ q H₁ H₂)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiberProjection
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev tensorRho₁ := BalancedTensor.complexMap (k := k)
  (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
  (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q)

abbrev tensorRho₂ := BalancedTensor.complexMap (k := k)
  (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
  (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ATwistedTensorExt
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem evaluatedTwistExt_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q) (n : ℕ)
    (x : Resolution.ASelfExt q (3*n)) :
    selfExtIso (k := k) (evaluatedTwistIso q H) (3*n)
      (x.mapExactFunctor (evaluatedTwistFunctor q H)) = (((H⁻¹ : kˣ) : k)^n) • x := by
  have he := evaluatedTwistEndpoint_eq q H
  have hh := ResolutionProducts.exactFunctor_action_natIso (k := k)
    (evaluatedTwistFunctor q H) (Resolution.aInverseRestriction q H)
    (twistedEnvelopingRestrictionIso (sourceTwist q H))
    (ModuleBar.nativeResolution k (A k q) (A.Simple q))
    (Resolution.aInverseEndpoint q H) (3*n) x
  erw [← he] at hh
  exact hh.trans (Resolution.aInverseTwist_standard_scalar q H hq hq1 hp n x)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_ATwistedCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwist_inverse :
    (HomotopyCategory.quotient _ _).map (completeTwistIn q H ≫ completeTwistOut q H) = 𝟙 _ :=
  BalancedTensor.completeAction_inverse (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwistOut_quotient :
    (HomotopyCategory.quotient _ _).map (completeTwistOut q H) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)).hom :=
  BalancedTensor.completeActionOut_quotient (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

theorem completeTwist_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (hp : Resolution.NoPositivePowerOne q) (m : ℕ) (hm : 0 < m)
    (x : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) ((3*m : ℕ) : ℤ)) :
    fullHomPostcomp (completeTwistOut q H) _
      (fullHomPrecomp (completeTwistIn q H) _
        (mapFullHom (evaluatedTwistFunctor q H) _ _ _ x)) = (((H⁻¹ : kˣ) : k)^m) • x := by
  apply BalancedTensor.completeAction_scalar_positive (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) (3*m) (by omega)
  intro z
  rw [nativeEvaluationIso_eq]
  exact evaluatedTwistExt_scalar q H hq hq1 hp m z

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteMainCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev explicitAlgebra := ConvertedAlgebra k q
  (EnvelopingBimodule k (A k q) (finiteFiber q H₁ H₂).carrier)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberComponents
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Y₀" => fiberTarget q

variable (H₁ H₂ : kˣ)
local notation "U₁" => twistedFiniteModule (sourceTwist q H₁)
local notation "U₂" => twistedFiniteModule (sourceTwist q H₂)

def evaluatedMiddleInl : (X₀).carrier →ₗ[R₀] (evaluatedMiddle q H₁ H₂).carrier :=
  (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInl U₁ U₂ Y₀)).comp
    (evaluatedTwistEquiv q H₁).symm.toLinearMap

def evaluatedMiddleInr : (X₀).carrier →ₗ[R₀] (evaluatedMiddle q H₁ H₂).carrier :=
  (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInr U₁ U₂ Y₀)).comp
    (evaluatedTwistEquiv q H₂).symm.toLinearMap

def evaluatedFiberSecond : (evaluatedMiddle q H₁ H₂).carrier →ₗ[R₀]
    (FiniteLeftModule.evaluated X₀ Y₀).carrier :=
  FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberMap U₁ U₂ Y₀
    (normalizedLift q H₁) (normalizedLift q H₂)).hom

theorem middleToSimplePair_inl : (middleToSimplePair q H₁ H₂).comp
    (evaluatedMiddleInl q H₁ H₂) = LinearMap.inl R₀ (X₀).carrier (X₀).carrier := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (FiniteLeftModule.middlePairMap_inl X₀ U₁ U₂ Y₀)
    ((evaluatedTwistEquiv q H₁).symm x)
  simp only [LinearMap.comp_apply] at h
  change (evaluatedTwistPairEquiv q H₁ H₂)
    ((FiniteLeftModule.middlePairMap X₀ U₁ U₂ Y₀)
      (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInl U₁ U₂ Y₀)
        ((evaluatedTwistEquiv q H₁).symm x))) = _
  rw [h]
  change ((evaluatedTwistEquiv q H₁) ((evaluatedTwistEquiv q H₁).symm x),
    (evaluatedTwistEquiv q H₂) 0) = (x,0)
  simp

theorem middleToSimplePair_inr : (middleToSimplePair q H₁ H₂).comp
    (evaluatedMiddleInr q H₁ H₂) = LinearMap.inr R₀ (X₀).carrier (X₀).carrier := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (FiniteLeftModule.middlePairMap_inr X₀ U₁ U₂ Y₀)
    ((evaluatedTwistEquiv q H₂).symm x)
  simp only [LinearMap.comp_apply] at h
  change (evaluatedTwistPairEquiv q H₁ H₂)
    ((FiniteLeftModule.middlePairMap X₀ U₁ U₂ Y₀)
      (FiniteLeftModule.evaluationMap X₀ (FiniteLeftModule.fiberSourceInr U₁ U₂ Y₀)
        ((evaluatedTwistEquiv q H₂).symm x))) = _
  rw [h]
  change ((evaluatedTwistEquiv q H₁) 0,
    (evaluatedTwistEquiv q H₂) ((evaluatedTwistEquiv q H₂).symm x)) = (0,x)
  simp

end ArExplicit.T

end

end OAI
end


