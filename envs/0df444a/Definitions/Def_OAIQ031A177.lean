-- Prove2me | Definitions.Def_OAIQ031A177
-- name    : OAIQ031A177
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:45:52.974443+00:00
-- url     : https://prove2.me/theorems/b2f67a13-b6df-438f-87c5-97c2db4e925b
-- title:
--   Definitions bundle OAIQ031A177 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 5 definitions and 27 theorems. The definitions and types are `OAI.ArExplicit.T.firstCoverCocycle`, `OAI.ArExplicit.T.secondCoverCocycle`, `OAI.ArExplicit.T.simpleNativeResolutionHom`, `OAI.ArExplicit.T.twoConeBottomCoordinate`, `OAI.ArExplicit.T.twoConeTopCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConcreteTwoConeCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedAdjacentComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedAdjacentComponents.lean), [`AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedConnectingCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleCoordinates.lean), [`AuslanderReiten_Ext_SimpleCoverExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/SimpleCoverExt.lean), [`AuslanderReiten_Resolutions_ConcreteNativeResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteNativeResolution.lean), [`AuslanderReiten_Resolutions_SimpleCoverCubicConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/SimpleCoverCubicConjugate.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A167`, `OAIQ031A168`, `OAIQ031A169`, `OAIQ031A170` and `OAIQ031A171` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A181`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A167
import Definitions.Def_OAIQ031A168
import Definitions.Def_OAIQ031A169
import Definitions.Def_OAIQ031A170
import Definitions.Def_OAIQ031A171

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeCoordinates
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "H" => CohomologyClass (A.simpleComplete q) (A.simpleComplete q)

def twoConeBottomCoordinate (a : ℤ) : twoConeBottomHom q a ≃ₗ[k] H a :=
  (evaluatedBaseFullHomEquiv q 0 a).trans
    (TateKoszul.degreeEquiv H (by omega))

def twoConeTopCoordinate (a : ℤ) : twoConeTopHom q a ≃ₗ[k] H (a-4) :=
  evaluatedBaseFullHomEquiv q 4 a

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedMiddleCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q

attribute [local instance] OAI.ArExplicit.T.middleCoordinateBaseScalar OAI.ArExplicit.T.middleCoordinateBaseTower OAI.ArExplicit.T.middleCoordinateScalar OAI.ArExplicit.T.middleCoordinateTower
theorem evaluatedRow_coordinates (n : ℕ) :
    FiniteLeftModule.evaluationMap X
      (M := TwoCone.middleCokernelModule D hf (n+1))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.rowCokernelMap D n) =
    (FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+3))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.firstCokernelMap D n)).comp
        (evaluatedSingletonFst q (n+1)) +
    (FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+3))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.secondCokernelMap D n)).comp
        (evaluatedSingletonSnd q (n+1)) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D n b.value.1 + TwoCone.secondCokernelMap D n b.value.2⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x =
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D n b.value.1⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x +
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.secondCokernelMap D n b.value.2⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x
  exact BalancedTensor.add_tmul _ _ _

theorem evaluatedColumn_snd (n : ℕ) :
    (evaluatedSingletonSnd q n).comp
      (FiniteLeftModule.evaluationMap X
        (M := TwoCone.baseCokernelModule D hf (n+5))
        (N := TwoCone.middleCokernelModule D hf n) (-(TwoCone.columnCokernelMap D n))) =
    FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+5))
      (N := TwoCone.baseCokernelModule D hf (n+2)) (TwoCone.firstCokernelMap D (n+2)) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨-(-(TwoCone.firstCokernelMap D (n+2) b.value))⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x =
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D (n+2) b.value⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x
  rw [neg_neg]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedAdjacentComponents
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem evaluatedAdjacentMap_snd (n : ℕ) :
    (evaluatedSingletonSnd q n).comp (evaluatedAdjacentMap q n) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.firstCokernelMap D₀ (n+2)) := evaluatedColumn_snd q n

theorem evaluatedAdjacentHom_snd (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)) ≫
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) =
    TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ (n+2) := by
  rw [← FiniteLeftModule.resolutionMap_comp, evaluatedAdjacentMap_snd]
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem evaluatedSingletonFst_step (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) ≫
      (evaluatedBaseStepIso q (n+2)).hom =
    (TwoCone.evaluatedMiddleSuccessorIso D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀
          (evaluatedSingletonFst q (n+1))))⟦(1 : ℤ)⟧' := by
  rw [evaluatedSingletonFst_eq, evaluatedSingletonFst_eq]
  exact TwoCone.evaluatedMiddleProjection_step D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ true n

theorem evaluatedSingletonSnd_step (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) ≫
      (evaluatedBaseStepIso q (n+2)).hom =
    (TwoCone.evaluatedMiddleSuccessorIso D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀
          (evaluatedSingletonSnd q (n+1))))⟦(1 : ℤ)⟧' := by
  rw [evaluatedSingletonSnd_eq, evaluatedSingletonSnd_eq]
  exact TwoCone.evaluatedMiddleProjection_step D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ false n

theorem simpleSkeletonConnecting_components (n : ℕ) :
    (simpleSkeletonTriangle q n).mor₃ =
      ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) ≫
        (evaluatedBaseStepIso q (n+2)).hom) ≫
          (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦(1 : ℤ)⟧' +
      ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)) ≫
        (evaluatedBaseStepIso q (n+2)).hom) ≫
          (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦(1 : ℤ)⟧' := by
  exact rowBoundary
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (1 : ℤ))
    _ _ _ _ _ _ _ _ _ _
    (resolutionRow τ₀ (M := evaluatedSingletonModule q (n+1))
      (N := evaluatedBaseModule q (n+3)) (P := evaluatedBaseModule q n)
      (evaluatedSingletonFst q (n+1)) (evaluatedSingletonSnd q (n+1))
      _ _ _ (evaluatedRow_coordinates q n))
    (TwoCone.evaluatedSkeletonConnecting_eq D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n)
    (evaluatedSingletonFst_step q n) (evaluatedSingletonSnd_step q n)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_SimpleCoverExt
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q

def firstCoverCocycle : (simpleOrdinaryResolution q).complex.X 3 ⟶ (X₀).carrier :=
  ModuleCat.ofHom (X := (simpleOrdinaryResolution q).complex.X 3) (Y := (X₀).carrier) ((firstCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3))
def secondCoverCocycle : (simpleOrdinaryResolution q).complex.X 3 ⟶ (X₀).carrier :=
  ModuleCat.ofHom (X := (simpleOrdinaryResolution q).complex.X 3) (Y := (X₀).carrier) ((secondCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3))

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverCocycle_closed :
    (simpleOrdinaryResolution q).complex.d 4 3 ≫ firstCoverCocycle q = 0 := by
  apply ModuleCat.hom_ext
  change ((firstCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)).comp
    (TwoCone.evaluatedBaseDifferential D₀ hf₀ X₀ 3) = 0
  rw [LinearMap.comp_assoc, TwoCone.evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverCocycle_closed :
    (simpleOrdinaryResolution q).complex.d 4 3 ≫ secondCoverCocycle q = 0 := by
  apply ModuleCat.hom_ext
  change ((secondCubicBack q).comp (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)).comp
    (TwoCone.evaluatedBaseDifferential D₀ hf₀ X₀ 3) = 0
  rw [LinearMap.comp_assoc, TwoCone.evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverClass_ext (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q) =
      (Ext.mk₀ (evaluatedBaseZeroEquiv q).toModuleIso.inv).comp
        ((simpleOrdinaryResolution q).extMk (firstCoverCocycle q) 4 rfl
          (firstCoverCocycle_closed q))
        (zero_add _) := by
  have h := TwoCone.evaluatedCover_ext_canonical (k := k) (R := R₀) D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (evaluatedBaseZeroEquiv q).symm.toLinearMap 2 (firstCubicBack q)
  exact h

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverClass_ext (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q) =
      (Ext.mk₀ (evaluatedBaseZeroEquiv q).toModuleIso.inv).comp
        ((simpleOrdinaryResolution q).extMk (secondCoverCocycle q) 4 rfl
          (secondCoverCocycle_closed q))
        (zero_add _) := by
  have h := TwoCone.evaluatedCover_ext_canonical (k := k) (R := R₀) D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (evaluatedBaseZeroEquiv q).symm.toLinearMap 2 (secondCubicBack q)
  exact h

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem firstCoverCocycle_eq :
    firstCoverCocycle q = ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0) ≫
      (simpleOrdinaryResolution q).π.f 0 ≫ (evaluatedBaseZeroEquiv q).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  change (evaluatedBaseZeroEquiv q).toLinearMap.comp
    ((FiniteLeftModule.evaluationMap X₀ (TwoCone.firstCokernelMap D₀ 0)).comp
      (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)) =
    (evaluatedBaseZeroEquiv q).toLinearMap.comp
      ((TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 0).comp
        (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
  rw [TwoCone.evaluatedFirstBaseMap_quotient]

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem secondCoverCocycle_eq :
    secondCoverCocycle q = ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0) ≫
      (simpleOrdinaryResolution q).π.f 0 ≫ (evaluatedBaseZeroEquiv q).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  change (evaluatedBaseZeroEquiv q).toLinearMap.comp
    ((FiniteLeftModule.evaluationMap X₀ (TwoCone.secondCokernelMap D₀ 0)).comp
      (TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 3)) =
    (evaluatedBaseZeroEquiv q).toLinearMap.comp
      ((TwoCone.evaluatedBaseQuotient D₀ hf₀ X₀ 0).comp
        (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
  rw [TwoCone.evaluatedSecondBaseMap_quotient]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteNativeResolution
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "A₀" => A k q

def simpleNativeResolutionHom : ProjectiveResolution.Hom (simpleOrdinaryResolution q)
    (simpleNativeTensorResolution q)
    ((evaluatedBaseZeroEquiv q).toModuleIso.hom ≫ (nativeToCanonicalSimple q).hom) where
  hom := (simpleNativeBarIso q).hom
  hom_f_zero_comp_π_f_zero := simpleNativeBarIso_augmentation q

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_SimpleCoverCubicConjugate
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
local notation "T₀" => T k q
local notation "S₀" => Resolution.Simple q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q

theorem firstCoverConjugateComparison :
    type_of% (firstCoverConjugateStart q (simpleNativeResolutionHom q)) :=
  firstCoverConjugateStart q (simpleNativeResolutionHom q)

theorem firstCoverConjugateCocycle :
    type_of% (firstCoverConjugateComparison q
      (ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
      (firstCoverCocycle q) (firstCoverCocycle_closed q) (firstCoverCocycle_eq q)) :=
  firstCoverConjugateComparison q
    (ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D₀ hf₀ X₀ 0))
    (firstCoverCocycle q) (firstCoverCocycle_closed q) (firstCoverCocycle_eq q)

theorem firstCoverConjugateProof :
    type_of% (firstCoverConjugateCocycle q (simpleNativeBarIso_first q 0)) :=
  firstCoverConjugateCocycle q (simpleNativeBarIso_first q 0)

theorem firstCoverCocycle_conjugate : type_of% (firstCoverConjugateProof q) :=
  firstCoverConjugateProof q

theorem secondCoverConjugateComparison :
    type_of% (secondCoverConjugateStart q (simpleNativeResolutionHom q)) :=
  secondCoverConjugateStart q (simpleNativeResolutionHom q)

theorem secondCoverConjugateCocycle :
    type_of% (secondCoverConjugateComparison q
      (ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
      (secondCoverCocycle q) (secondCoverCocycle_closed q) (secondCoverCocycle_eq q)) :=
  secondCoverConjugateComparison q
    (ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D₀ hf₀ X₀ 0))
    (secondCoverCocycle q) (secondCoverCocycle_closed q) (secondCoverCocycle_eq q)

theorem secondCoverConjugateProof :
    type_of% (secondCoverConjugateCocycle q (simpleNativeBarIso_second q 0)) :=
  secondCoverConjugateCocycle q (simpleNativeBarIso_second q 0)

theorem secondCoverCocycle_conjugate : type_of% (secondCoverConjugateProof q) :=
  secondCoverConjugateProof q

theorem firstCoverClass_conjugate (hq1 : 1+q ≠ 0) :
    selfExtIso (k := k) (nativeToCanonicalSimple q) 3
      (A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q)) =
      Resolution.aCanonicalFirst q := by
  rw [firstCoverClass_ext]
  dsimp only [Resolution.aCanonicalFirst]
  exact firstCoverCocycle_conjugate q

theorem secondCoverClass_conjugate (hq1 : 1+q ≠ 0) :
    selfExtIso (k := k) (nativeToCanonicalSimple q) 3
      (A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q)) =
      Resolution.aCanonicalSecond q := by
  rw [secondCoverClass_ext]
  dsimp only [Resolution.aCanonicalSecond]
  exact secondCoverCocycle_conjugate q

theorem firstCoverClass_ext_eq (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q) = Resolution.aFirst q := by
  exact ModuleBar.tensorFirst_eq_of_conjugate k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (A.fullNonnegativeExtEquiv q hq1 3 (firstCoverClass q))
    (firstCoverClass_conjugate q hq1)

theorem secondCoverClass_ext_eq (hq1 : 1+q ≠ 0) :
    A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q) = Resolution.aSecond q := by
  exact ModuleBar.tensorSecond_eq_of_conjugate k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (A.fullNonnegativeExtEquiv q hq1 3 (secondCoverClass q))
    (secondCoverClass_conjugate q hq1)

theorem firstCoverClass_eq (hq1 : 1+q ≠ 0) :
    firstCoverClass q = A.firstFullClass q hq1 := by
  apply (A.fullNonnegativeExtEquiv q hq1 3).injective
  exact (firstCoverClass_ext_eq q hq1).trans
    ((A.fullNonnegativeExtEquiv q hq1 3).apply_symm_apply _).symm

theorem secondCoverClass_eq (hq1 : 1+q ≠ 0) :
    secondCoverClass q = A.secondFullClass q hq1 := by
  apply (A.fullNonnegativeExtEquiv q hq1 3).injective
  exact (secondCoverClass_ext_eq q hq1).trans
    ((A.fullNonnegativeExtEquiv q hq1 3).apply_symm_apply _).symm

end ArExplicit.T

end

end OAI
end


