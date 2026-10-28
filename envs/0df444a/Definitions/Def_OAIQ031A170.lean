-- Prove2me | Definitions.Def_OAIQ031A170
-- name    : OAIQ031A170
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:26:24.061741+00:00
-- url     : https://prove2.me/theorems/d0e18b88-2fc2-4bc9-81c2-23b5d9af09fc
-- title:
--   Definitions bundle OAIQ031A170 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 19 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.T.concreteTwoConeFiltration`, `OAI.ArExplicit.T.evaluatedBaseFullHomEquiv`, `OAI.ArExplicit.T.evaluatedBaseHomEquiv`, `OAI.ArExplicit.T.evaluatedBaseIteration`, `OAI.ArExplicit.T.evaluatedBaseStepIso`, `OAI.ArExplicit.T.evaluatedBaseZeroResolutionIso`, `OAI.ArExplicit.T.firstCoverClass`, `OAI.ArExplicit.T.firstCoverOperator`, `OAI.ArExplicit.T.firstCubicBack`, `OAI.ArExplicit.T.secondCoverClass`, `OAI.ArExplicit.T.secondCoverOperator`, `OAI.ArExplicit.T.secondCubicBack`, `OAI.ArExplicit.T.simpleCoverClass`, `OAI.ArExplicit.T.simpleToEvaluatedBaseShiftIso`, `OAI.ArExplicit.T.twoConeBottomHom`, `OAI.ArExplicit.T.twoConeHom`, `OAI.ArExplicit.T.twoConeMiddleHom`, `OAI.ArExplicit.T.twoConeSkeletonHom`, `OAI.ArExplicit.T.twoConeTopHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConcreteTwoConeCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeCoordinates.lean), [`AuslanderReiten_Coordinates_TensorFiniteTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteTop.lean), [`AuslanderReiten_Coordinates_TensorNormalizedTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorNormalizedTop.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluatedConeShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluatedConeShift.lean), [`AuslanderReiten_Evaluation_EvaluatedBaseShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedBaseShift.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverStep`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverStep.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleShift.lean), [`AuslanderReiten_Resolutions_ConcreteKoszulCoordinateLaws`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ConcreteKoszulCoordinateLaws.lean), [`AuslanderReiten_Resolutions_SimpleCoverClasses`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/SimpleCoverClasses.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A163`, `OAIQ031A164` and `OAIQ031A165` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A175`, `OAIQ031A176` and `OAIQ031A177`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A163
import Definitions.Def_OAIQ031A164
import Definitions.Def_OAIQ031A165

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedBaseShift
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)

def evaluatedBaseZeroResolutionIso : evaluatedBaseResolution q 0 ≅
    (Q).obj ((X).completeCochain τ) :=
  FiniteLeftModule.resolutionIso (M := evaluatedBaseModule q 0) (N := X) τ
    (evaluatedBaseZeroEquiv q)

def evaluatedBaseStepIso (n : ℕ) : evaluatedBaseResolution q n ≅
    (evaluatedBaseResolution q (n+1))⟦(1 : ℤ)⟧ :=
  TwoCone.evaluatedBaseSuccessorIso D hf (bimodule_exact q) (baseTail_right_projective q)
    (bimodule_term_projective q) X τ n

def evaluatedBaseIteration (n : ℕ) : evaluatedBaseResolution q 0 ≅
    (evaluatedBaseResolution q n)⟦(n : ℤ)⟧ :=
  iteratedShiftIso (evaluatedBaseResolution q) (evaluatedBaseStepIso q) n

def simpleToEvaluatedBaseShiftIso (n : ℕ) : (Q).obj ((X).completeCochain τ) ≅
    (evaluatedBaseResolution q n)⟦(n : ℤ)⟧ :=
  (evaluatedBaseZeroResolutionIso q).symm ≪≫ evaluatedBaseIteration q n

theorem simpleToEvaluatedBaseShiftIso_succ (n : ℕ) :
    (simpleToEvaluatedBaseShiftIso q (n+1)).hom =
      (simpleToEvaluatedBaseShiftIso q n).hom ≫
        (CategoryTheory.shiftFunctor HC (n : ℤ)).map (evaluatedBaseStepIso q n).hom ≫
          (CategoryTheory.shiftFunctorAdd' HC (1 : ℤ) (n : ℤ)
            ((n+1 : ℕ) : ℤ) (by omega)).inv.app (evaluatedBaseResolution q (n+1)) := by
  simp only [simpleToEvaluatedBaseShiftIso, evaluatedBaseIteration, iteratedShiftIso,
    Iso.trans_hom, Category.assoc, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]

open scoped ModuleCat.Algebra

def evaluatedBaseHomEquiv (n : ℕ) (a : ℤ) :
    ((Q).obj ((X).completeCochain τ) ⟶ (evaluatedBaseResolution q n)⟦a⟧) ≃ₗ[k]
      ((Q).obj ((X).completeCochain τ) ⟶ ((Q).obj ((X).completeCochain τ))⟦a-(n : ℤ)⟧) :=
  shiftedNegativeHomEquiv (n : ℤ) (simpleToEvaluatedBaseShiftIso q n) k _ a

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedMiddleShift
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "SX" => evaluatedSimpleObject q

def evaluatedBaseFullHomEquiv (n : ℕ) (a : ℤ) :
    (SX ⟶ (evaluatedBaseResolution q n)⟦a⟧) ≃ₗ[k]
      CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (a-(n:ℤ)) :=
  (evaluatedBaseHomEquiv q n a).trans
    (fullHomShiftedHomotopyEquiv k (A.simpleComplete q) (A.simpleComplete q) (a-(n:ℤ))).symm

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeCoordinates
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev twoConeBottomHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₁)⟦a⟧
abbrev twoConeMiddleHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₃)⟦a⟧
abbrev twoConeTopHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleTopTriangle q 0).obj₃)⟦a⟧
abbrev twoConeSkeletonHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleSkeletonTriangle q 0).obj₂)⟦a⟧
abbrev twoConeHom (a : ℤ) :=
  evaluatedSimpleObject q ⟶ ((simpleTopTriangle q 0).obj₂)⟦a⟧

def concreteTwoConeFiltration : TwoConeFiltration (k := k)
    (twoConeBottomHom q) (twoConeMiddleHom q) (twoConeTopHom q)
    (twoConeSkeletonHom q) (twoConeHom q) :=
  simpleHomFiltration q 0

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteTop
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q
local notation "Q" => sourceData q H
local notation "τ" => AEnvelopingFrobeniusTrace k q
local notation "hD" => bimodule_term_finite_k q
local notation "hQ" => source_term_finite_k q H

theorem topFourShift_natural :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 0) (N := TwoCone.baseCokernelModule D hD 1)
      (bimoduleTopCokernel q H 0)) ≫ (topFourShiftIso q).hom =
    (TwoCone.baseIteratedShiftIso Q hQ τ (source_exact q H) (source_projective q H) 4).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (4 : ℤ)).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
          (bimoduleTopCokernel q H 4))) := by
  have h := iteratedShiftIso_natural
    (Y := TwoCone.baseResolution Q hQ τ)
    (s := TwoCone.baseSuccessorShiftIso Q hQ τ (source_exact q H) (source_projective q H))
    (Z := fun n => TwoCone.baseResolution D hD τ (n+1))
    (fun n => TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q) (bimodule_term_projective q) (n+1))
    (fun n => (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ n) (N := TwoCone.baseCokernelModule D hD (n+1))
      (bimoduleTopCokernel q H n))) (topOneShift_natural q H) 4
  simp only [topFourShiftIso, TwoCone.baseIteratedShiftIso_eq_iterated, Nat.cast_ofNat] at h ⊢
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

theorem resolutionTailTop :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 4) (N := firstTailModule q) (sourceFourthToTail q H)) ≫
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := firstTailModule q) (N := TwoCone.baseCokernelModule D hD 5) (TwoCone.topCokernelMap D 1)) =
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
      (bimoduleTopCokernel q H 4)) := by
  calc
    _ = (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5)
        ((TwoCone.topCokernelMap D 1).comp (sourceFourthToTail q H))) :=
      (FiniteLeftModule.resolutionMap_comp τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := firstTailModule q)
        (L := TwoCone.baseCokernelModule D hD 5)
        (sourceFourthToTail q H) (TwoCone.topCokernelMap D 1)).symm
    _ = _ := congrArg (fun f => (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := TwoCone.baseCokernelModule Q hQ 4) (N := TwoCone.baseCokernelModule D hD 5) f))
      (sourceFourthToTail_top q H)

theorem finiteLift_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ (finiteLift q H)) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ (finiteSourceTop q H)) := by
  rw [finiteLift_spec]
  dsimp only [finiteLiftClass, FiniteLeftModule.shiftedResolutionMap, finiteTargetTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Nat.cast_ofNat]
  erw [← Functor.map_comp_assoc]
  rw [resolutionTailTop q H]
  simp only [sourceShiftIso, TwoCone.tailSourceShiftIso, Iso.trans_hom, Category.assoc]
  have h := congrArg (fun f => f ≫ (topFourShiftIso q).inv) (topFourShift_natural q H)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [← h, FiniteLeftModule.resolutionIso_hom]
  exact (FiniteLeftModule.resolutionMap_comp τ
    (M := twistedFiniteModule (sourceTwist q H)) (N := TwoCone.baseCokernelModule Q hQ 0)
    (L := TwoCone.baseCokernelModule D hD 1)
    (sourceAugmentationEquiv q H).toLinearMap (bimoduleTopCokernel q H 0)).symm

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorNormalizedTop
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "D" => bimoduleTwoConeData q
local notation "τ" => AEnvelopingFrobeniusTrace k q
local notation "hD" => bimodule_term_finite_k q

theorem normalizedLift_top :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := (firstTailModule q).canonicalCosyzygies 4) (normalizedLift q H).hom) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := TwoCone.baseCokernelModule D hD 1) (normalizedSourceTop q H)) := by
  change (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := (firstTailModule q).canonicalCosyzygies 4) (((H : k)^2)⁻¹ • finiteLift q H)) ≫ finiteTargetTop q =
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ
        (M := twistedFiniteModule (sourceTwist q H))
        (N := TwoCone.baseCokernelModule D hD 1) (((H : k)^2)⁻¹ • finiteSourceTop q H))
  rw [FiniteLeftModule.resolutionMap_smul, Linear.smul_comp, finiteLift_top,
    FiniteLeftModule.resolutionMap_smul]

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluatedConeShift
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τe₀" => AEnvelopingFrobeniusTrace k q

theorem coneCokernel_right_projective (n : ℕ) : Module.Projective R₀ᵐᵒᵖ
    (EnvelopingBimodule k R₀ (TwoCone.cokernelModule D₀ hf₀ n).carrier) := by
  let j := tensorRightInclusion k R₀ R₀ᵐᵒᵖ
  have hp (m : ℕ) : Module.Projective R₀ᵐᵒᵖ (TwoCone.BaseCokernel ((D₀).restrict j) m) := by
    let := baseTail_right_projective q m
    exact Module.Projective.of_equiv
      ((EnvelopingBimodule.rightEquiv (TwoCone.baseCokernelModule D₀ hf₀ m).carrier).trans
        (TwoCone.baseCokernelRestrictionEquiv j D₀ m))
  let := TwoCone.cokernel_projective ((D₀).restrict j)
    (TwoCone.restricted_exact j D₀ (bimodule_exact q)) hp n
  exact Module.Projective.of_equiv
    ((EnvelopingBimodule.rightEquiv (TwoCone.cokernelModule D₀ hf₀ n).carrier).trans
      (TwoCone.cokernelRestrictionEquiv j D₀ n)).symm

theorem firstTailCosyzygies_right_projective (n : ℕ) : Module.Projective R₀ᵐᵒᵖ
    (EnvelopingBimodule k R₀ ((firstTailModule q).canonicalCosyzygies n).carrier) := by
  let := firstTailModule_right_finite q
  let := firstTailModule_right_projective q
  let := tensorRightRegular_finite k R₀ R₀ᵐᵒᵖ
  let := tensorRightRegular_projective k R₀ R₀ᵐᵒᵖ
  obtain ⟨hfin, hproj⟩ := (firstTailModule q).canonicalCosyzygies_side
    (tensorRightInclusion k R₀ R₀ᵐᵒᵖ) τe₀ n
  let := hproj
  infer_instance

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverStep
attribute [-instance] _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "H₀" => fun d => CohomologyClass (A.simpleComplete q) (A.simpleComplete q) d

theorem evaluatedBaseFullHomEquiv_step (n : ℕ) (a : ℤ)
    (v : evaluatedSimpleObject q ⟶ (evaluatedBaseResolution q n)⟦a⟧) :
    evaluatedBaseFullHomEquiv q (n+1) (a+1)
      (ShiftedHom.comp v (evaluatedBaseStepIso q n).hom (add_comm 1 a)) =
    TateKoszul.degreeEquiv (k := k) H₀ (by omega : a-(n:ℤ)=(a+1)-((n+1:ℕ):ℤ))
      (evaluatedBaseFullHomEquiv q n a v) := by
  exact coverStepFullHom k _ _ (n:ℤ) ((n+1:ℕ):ℤ) (by omega)
    (simpleToEvaluatedBaseShiftIso q n) (evaluatedBaseStepIso q n)
    (simpleToEvaluatedBaseShiftIso q (n+1)) (simpleToEvaluatedBaseShiftIso_succ q n) a v

end ArExplicit.T

end

end OAI
end

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

abbrev simpleCoverClass (n : ℕ) :=
  (TwoCone.evaluatedCoverTower D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q)).coverClassFrom τ₀ X₀
    (CohomologyClass.mk (Cocycle.ofHom
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedBaseZeroEquiv q).symm.toLinearMap))) n

theorem simpleCoverClass_hom (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ) (simpleCoverClass q n) =
      (simpleToEvaluatedBaseShiftIso q n).hom :=
  TwoCone.evaluatedCoverTower_coverClassFrom_hom D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (FiniteLeftModule.resolutionMap τ₀ (evaluatedBaseZeroEquiv q).symm.toLinearMap) n

def firstCubicBack : (evaluatedBaseModule q 3).carrier →ₗ[R₀] (X₀).carrier :=
  (evaluatedBaseZeroEquiv q).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ 3)
      (N := TwoCone.baseCokernelModule D₀ hf₀ 0) (TwoCone.firstCokernelMap D₀ 0))

def secondCubicBack : (evaluatedBaseModule q 3).carrier →ₗ[R₀] (X₀).carrier :=
  (evaluatedBaseZeroEquiv q).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ 3)
      (N := TwoCone.baseCokernelModule D₀ hf₀ 0) (TwoCone.secondCokernelMap D₀ 0))

def firstCoverClass : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 3 :=
  fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (firstCubicBack q)) 3 (simpleCoverClass q 3)

def secondCoverClass : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 3 :=
  fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (secondCubicBack q)) 3 (simpleCoverClass q 3)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteKoszulCoordinateLaws
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

abbrev firstCoverOperator (a : ℤ) :=
  fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (firstCoverClass q)
abbrev secondCoverOperator (a : ℤ) :=
  fullHomRightMultiply (k := k) (K := A.simpleComplete q) (n := a) (secondCoverClass q)

end ArExplicit.T

end

end OAI
end


