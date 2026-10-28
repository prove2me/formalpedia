-- Prove2me | Definitions.Def_OAIQ031A181
-- name    : OAIQ031A181
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:58:37.661966+00:00
-- url     : https://prove2.me/theorems/237f6f25-79a3-4e25-a8d2-5975e0203194
-- title:
--   Definitions bundle OAIQ031A181 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 2 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.T.branchZeroHom`, `OAI.ArExplicit.T.coverTateModel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConcreteTwoConeProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeProfile.lean), [`AuslanderReiten_Coordinates_ConcreteCubicStepAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteCubicStepAction.lean), [`AuslanderReiten_Evaluation_ConcreteTensorFiberMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteTensorFiberMaps.lean), [`AuslanderReiten_Evaluation_EvaluatedAdjacentComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedAdjacentComponents.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverStep`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverStep.lean), [`AuslanderReiten_Fibers_ConcreteFiberRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ConcreteFiberRow.lean), [`AuslanderReiten_Fibers_FiberBranchConsequences`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberBranchConsequences.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulColumn`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulColumn.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A175`, `OAIQ031A176`, `OAIQ031A177` and `OAIQ031A178` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A183`, `OAIQ031A184` and `OAIQ031A185`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A175
import Definitions.Def_OAIQ031A176
import Definitions.Def_OAIQ031A177
import Definitions.Def_OAIQ031A178

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverStep
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "R₀" => A k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

theorem evaluatedSingletonFullHomEquiv_snd (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedSingletonResolution q n)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q n a v).2 =
      evaluatedBaseFullHomEquiv q (n+2) a
        (v ≫ ((Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)))⟦a⟧') := by
  simp only [evaluatedSingletonFullHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, evaluatedSingletonHomEquiv,
    mappedBiproductHomEquiv_fst, mappedBiproductHomEquiv_snd,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom]
  change evaluatedBaseFullHomEquiv q (n+2) a
    ((v ≫ (evaluatedSingletonProductIso q n).hom⟦a⟧') ≫ biprod.snd⟦a⟧') = _
  rw [Category.assoc, ← Functor.map_comp, evaluatedSingletonProductIso_snd]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteCubicStepAction
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem evaluatedFirstCokernel_step_action (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) :
    evaluatedBaseFullHomEquiv q n (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a) ≫
        (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ n)⟦a+1⟧') =
      TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-((n+2:ℕ):ℤ)+3=(a+1)-(n:ℤ))
        (fullHomProduct (evaluatedBaseFullHomEquiv q (n+2) a v) (firstCoverClass q)) := by
  have h := evaluatedFirstCokernel_fullHom_action q n (a+1)
    (ShiftedHom.comp v (evaluatedBaseStepIso q (n+2)).hom (add_comm 1 a))
  have hs := evaluatedBaseFullHomEquiv_step q (n+2) a v
  exact fullHomProduct_coordinate _ _ (by omega) hs h

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedAdjacentComponents
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem simpleTopConnecting_snd (n : ℕ) :
    (simpleTopTriangle q n).mor₃ ≫
      ((simpleSkeletonTriangle q n).mor₂ ≫
        (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (evaluatedSingletonSnd q n)))⟦(1 : ℤ)⟧' =
    (evaluatedBaseStepIso q (n+4)).hom ≫
      (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ (n+2))⟦(1 : ℤ)⟧' := by
  erw [Functor.map_comp, ← Category.assoc, simpleTopConnecting_adjacent,
    Category.assoc, ← Functor.map_comp, evaluatedAdjacentHom_snd]
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulColumn
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem simpleTopColumn_snd_unsigned (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q 4)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v))).2 =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2)
      (fullHomProduct (evaluatedBaseFullHomEquiv q 4 a v) (firstCoverClass q)) := by
  erw [evaluatedSingletonFullHomEquiv_snd, TriangleGradedSequence.second_eq_shift,
    TriangleGradedSequence.connecting_eq_product, Category.assoc, ← Functor.map_comp,
    ← shiftedComp_post, simpleTopConnecting_snd, shiftedComp_post,
    evaluatedFirstCokernel_step_action]

theorem simpleTopColumn_snd (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q 4)⟦a⟧) :
    (evaluatedSingletonFullHomEquiv q 0 (a+1)
      (TriangleGradedSequence.second k (simpleSkeletonTriangle q 0) (evaluatedSimpleObject q)
        (a+1) (TriangleGradedSequence.connecting k (simpleTopTriangle q 0)
          (evaluatedSimpleObject q) a v))).2 =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2)
      (-(fullHomProduct (evaluatedBaseFullHomEquiv q 4 a v) (firstCoverClass q))) := by
  have h := simpleTopColumn_snd_unsigned q a v
  exact h.trans (congrArg
    (TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-4+3=(a+1)-2))
      (columnNeg (k := k) _).symm)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeProfile
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [HasDerivedCategory (ModuleCat.{u} (T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : Resolution.NoPositivePowerOne q)
include hq hq1 h

def coverTateModel : TateKoszul.Model (firstCoverOperator q) (secondCoverOperator q) := by
  unfold firstCoverOperator secondCoverOperator
  rw [firstCoverClass_eq q hq1, secondCoverClass_eq q hq1]
  exact A.tateModel q hq hq1 h

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteTensorFiberMaps
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

theorem tensorFiberRhoPair_comparison (n : ℤ)
    (x : CohomologyClass (A.simpleComplete q) (tensorFiberComplete q H₁ H₂) n) :
    tensorFiberRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (BalancedTensor.comparisonOut (AFrobeniusTrace k q)
          (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₁)) n
        (fullHomPostcomp (BalancedTensor.complexMap (k := k)
          (EnvelopingBimodule.mapRight (rho₁ q H₁ H₂))
          (EnvelopingBimodule.map_left_smul (rho₁ q H₁ H₂)) (A.simpleComplete q)) n x),
       fullHomPostcomp (BalancedTensor.comparisonOut (AFrobeniusTrace k q)
          (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H₂)) n
        (fullHomPostcomp (BalancedTensor.complexMap (k := k)
          (EnvelopingBimodule.mapRight (rho₂ q H₁ H₂))
          (EnvelopingBimodule.map_left_smul (rho₂ q H₁ H₂)) (A.simpleComplete q)) n x)) := by
  have h₁ := fullHomPostcomp_square k n (tensorFiberOut_rho₁ q H₁ H₂) x
  have h₂ := fullHomPostcomp_square k n (tensorFiberOut_rho₂ q H₁ H₂) x
  exact (tensorFiberRhoPair_apply q H₁ H₂ n x).trans (Prod.ext h₁.symm h₂.symm)

theorem tensorFiberMap_zero_nonzero_kernel
    (hq1 : 1+q ≠ 0)
    (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0) :
    ∃ w : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 0 ×
        CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 0,
      w ≠ 0 ∧ TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) 0 w = 0 := by
  apply TriangularInduction.tensorComparison_zero_nonzero_kernel
  intro h
  have hh := A.fullHomZeroScalarEquiv_identity q hq1
  rw [h, map_zero] at hh
  exact zero_ne_one hh

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ConcreteFiberRow
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
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)

def branchZeroHom (H : kˣ) : BranchHom q 0 :=
  branchHom q H ≫ (shiftFunctorZero HC ℤ).inv.app (branchTargetObject q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberBranchConsequences
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)
local notation "T₀" => fiberProductTriangle q H₁ H₂
local notation "X₀" => simpleHomotopyObject q

theorem branchZeroHom_ne_zero (H : kˣ) (hn : branchHom q H ≠ 0) :
    branchZeroHom q H ≠ 0 := by
  intro h
  apply hn
  apply (cancel_mono ((shiftFunctorZero HC ℤ).inv.app (branchTargetObject q))).1
  simpa only [branchZeroHom, Limits.zero_comp] using h

variable (hq1 : 1+q ≠ 0) (e : BranchHom q 0 ≃ₗ[k] k)
variable (hg : branchHom q H₁ = branchHom q H₂) (hn : branchHom q H₁ ≠ 0)

include hn in
theorem branchScalar_ne_zero : e (branchZeroHom q H₁) ≠ 0 := by
  intro hz
  exact branchZeroHom_ne_zero q H₁ hn (e.injective (hz.trans (map_zero e).symm))

end ArExplicit.T

end

end OAI
end


