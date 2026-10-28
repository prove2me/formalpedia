-- Prove2me | Definitions.Def_OAIQ031A176
-- name    : OAIQ031A176
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:51:29.460005+00:00
-- url     : https://prove2.me/theorems/e023579b-0743-4a5b-b32f-140cc6337db8
-- title:
--   Definitions bundle OAIQ031A176 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 11 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Coordinates_ConcreteCubicAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteCubicAction.lean), [`AuslanderReiten_Coordinates_ConcreteCubicStepAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteCubicStepAction.lean), [`AuslanderReiten_Evaluation_EvaluatedAdjacentComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedAdjacentComponents.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedTopConnecting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedTopConnecting.lean), [`AuslanderReiten_Evaluation_TensorEvaluatedTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorEvaluatedTop.lean), [`AuslanderReiten_Resolutions_SimpleCoverClasses`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/SimpleCoverClasses.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A169`, `OAIQ031A170` and `OAIQ031A171` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A180` and `OAIQ031A181`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A169
import Definitions.Def_OAIQ031A170
import Definitions.Def_OAIQ031A171

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_SimpleCoverClasses
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem firstCoverClass_hom :
    fullHomShiftedHomotopyEquiv k _ _ 3 (firstCoverClass q) =
      (simpleToEvaluatedBaseShiftIso q 3).hom ≫
        (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ 0 ≫ (evaluatedBaseZeroResolutionIso q).hom)⟦(3 : ℤ)⟧' := by
  erw [firstCoverClass, fullHomShiftedHomotopyEquiv_postcomp, simpleCoverClass_hom]
  congr 1
  apply congrArg (fun f => (CategoryTheory.shiftFunctor
    (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (3 : ℤ)).map f)
  change (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (firstCubicBack q)) = _
  exact FiniteLeftModule.resolutionMap_comp τ₀ _ _

theorem secondCoverClass_hom :
    fullHomShiftedHomotopyEquiv k _ _ 3 (secondCoverClass q) =
      (simpleToEvaluatedBaseShiftIso q 3).hom ≫
        (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ 0 ≫ (evaluatedBaseZeroResolutionIso q).hom)⟦(3 : ℤ)⟧' := by
  erw [secondCoverClass, fullHomShiftedHomotopyEquiv_postcomp, simpleCoverClass_hom]
  congr 1
  apply congrArg (fun f => (CategoryTheory.shiftFunctor
    (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (3 : ℤ)).map f)
  change (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (secondCubicBack q)) = _
  exact FiniteLeftModule.resolutionMap_comp τ₀ _ _

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteCubicAction
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "H₀" => fun n => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) n
local notation "SX" => simpleHomotopyObject_p0 q

theorem evaluatedFirstCokernel_fullHom_action (n : ℕ) (a : ℤ)
    (v : SX ⟶ (evaluatedBaseResolution q (n+3))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n a
      (v ≫ (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) H₀
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+3) a v) (firstCoverClass q)) := by
  exact coverFullHom_action k (A.simpleComplete q)
    (evaluatedBaseResolution q) (evaluatedBaseStepIso q) (evaluatedBaseZeroResolutionIso q).symm
    (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀)
    (TwoCone.evaluatedFirstCokernel_step D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀)
    (firstCoverClass q) (firstCoverClass_hom q) n a v

theorem evaluatedSecondCokernel_fullHom_action (n : ℕ) (a : ℤ)
    (v : SX ⟶ (evaluatedBaseResolution q (n+3))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n a
      (v ≫ (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) H₀
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+3) a v) (secondCoverClass q)) := by
  exact coverFullHom_action k (A.simpleComplete q)
    (evaluatedBaseResolution q) (evaluatedBaseStepIso q) (evaluatedBaseZeroResolutionIso q).symm
    (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀)
    (TwoCone.evaluatedSecondCokernel_step D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀)
    (secondCoverClass q) (secondCoverClass_hom q) n a v

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteCubicStepAction
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem evaluatedSecondCokernel_step_action (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a) ≫
        (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ n)⟦a+1⟧') =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-((n+2:ℕ):ℤ)+3=(a+1)-(n:ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+2) a v) (secondCoverClass q)) := by
  have h := evaluatedSecondCokernel_fullHom_action q n (a+1)
    (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a))
  have hs := evaluatedBaseFullHomEquiv_step q (n+2) a v
  exact fullHomProduct_coordinate _ _ (by omega) hs h

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedMiddleCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
theorem evaluatedColumn_fst (n : ℕ) :
    (evaluatedSingletonFst q n).comp
      (FiniteLeftModule.evaluationMap X
        (M := TwoCone.baseCokernelModule D hf (n+5))
        (N := TwoCone.middleCokernelModule D hf n) (-(TwoCone.columnCokernelMap D n))) =
    -(FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+5))
      (N := TwoCone.baseCokernelModule D hf (n+2)) (TwoCone.secondCokernelMap D (n+2))) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨-(TwoCone.secondCokernelMap D (n+2) b.value)⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x =
    -BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.secondCokernelMap D (n+2) b.value⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x
  change BalancedTensor.tmul (k := k) (R := R₀) (-_) x = _
  simp [BalancedTensor.tmul, TensorProduct.neg_tmul]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTopConnecting
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
universe u v

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem simpleTopConnecting_adjacent (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫ (simpleSkeletonTriangle q n).mor₂⟦(1 : ℤ)⟧' =
      (evaluatedBaseStepIso q (n+4)).hom ≫
        ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)))⟦(1 : ℤ)⟧' := by
  rw [simpleSkeletonTriangle_second]
  exact postBoundary
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (1 : ℤ))
    _ _ _ _ _
    (TwoCone.evaluatedTopConnecting_eq D₀ hf₀ (bimodule_exact q)
      (baseTail_right_projective q) (bimodule_term_projective q) X₀ τ₀ n)
    (resolutionComposite τ₀
      (M := evaluatedBaseModule q (n+5))
      (N := (X₀).evaluated (TwoCone.skeletonCokernelModule D₀ hf₀ n))
      (P := evaluatedSingletonModule q n) _ _ _ (evaluatedTopAdjacent q n))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedAdjacentComponents
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem evaluatedAdjacentMap_fst (n : ℕ) :
    (evaluatedSingletonFst q n).comp (evaluatedAdjacentMap q n) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.baseCokernelModule D₀ hf₀ (n+2))
      (TwoCone.secondCokernelMap D₀ (n+2)) := by
  have h := evaluatedColumn_fst q n
  refine h.trans ?_
  apply LinearMap.ext
  intro z
  exact charTwoNeg k _

theorem evaluatedAdjacentHom_fst (n : ℕ) :
    (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedAdjacentMap q n)) ≫
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)) =
    TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ (n+2) := by
  rw [← FiniteLeftModule.resolutionMap_comp, evaluatedAdjacentMap_fst]
  rfl

theorem simpleTopConnecting_fst (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫
      ((simpleSkeletonTriangle q n).mor₂ ≫
        (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonFst q n)))⟦(1 : ℤ)⟧' =
    (evaluatedBaseStepIso q (n+4)).hom ≫
      (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ (n+2))⟦(1 : ℤ)⟧' := by
  erw [Functor.map_comp, ← Category.assoc, simpleTopConnecting_adjacent,
    Category.assoc, ← Functor.map_comp, evaluatedAdjacentHom_fst]
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorEvaluatedTop
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)

theorem normalizedLift_evaluated_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
        (FiniteLeftModule.evaluationMap (A.simpleFiniteModule q)
          (M := twistedFiniteModule (sourceTwist q H)) (N := fiberTarget q)
          (normalizedLift q H).hom)) ≫ evaluatedFiniteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
        (FiniteLeftModule.evaluationMap (A.simpleFiniteModule q)
          (M := twistedFiniteModule (sourceTwist q H))
          (N := TwoCone.baseCokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1)
          (normalizedSourceTop q H))) := by
  exact FiniteLeftModule.evaluationResolutionMap_triangle (A.simpleFiniteModule q)
    (AEnvelopingFrobeniusTrace k q) (AFrobeniusTrace k q)
    (normalizedLift q H).hom (normalizedSourceTop q H) (finiteTargetTop q)
    (normalizedLift_top q H)

end ArExplicit.T

end

end OAI
end


