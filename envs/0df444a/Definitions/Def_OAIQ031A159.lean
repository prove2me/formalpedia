-- Prove2me | Definitions.Def_OAIQ031A159
-- name    : OAIQ031A159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:09:36.884614+00:00
-- url     : https://prove2.me/theorems/473ac238-0403-4063-a7b2-ab99861f2788
-- title:
--   Definitions bundle OAIQ031A159 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 17 definitions, 1 instance and 10 theorems. The definitions and types are `OAI.ArExplicit.Resolution.aInverseEndpoint`, `OAI.ArExplicit.Resolution.aInverseRestriction`, `OAI.ArExplicit.T.baseScalar`, `OAI.ArExplicit.T.evaluatedBaseModule`, `OAI.ArExplicit.T.evaluatedBaseResolution`, `OAI.ArExplicit.T.evaluatedTwistEquiv`, `OAI.ArExplicit.T.fiberTarget`, `OAI.ArExplicit.T.finiteLift`, `OAI.ArExplicit.T.normalizedLift`, `OAI.ArExplicit.T.sourceAugmentationEquiv`, `OAI.ArExplicit.T.sourceFourthToTail`, `OAI.ArExplicit.T.sourceShiftIso`, `OAI.ArExplicit.T.sourceUnit`, `OAI.ArExplicit.T.twistedSimpleEquiv`, `OAI.ArExplicit.TwoCone.baseIteratedShiftIso`, `OAI.ArExplicit.TwoCone.baseSuccessorShiftIso`, `OAI.ArExplicit.TwoCone.tailSourceShiftIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeModuleTriangles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeModuleTriangles.lean), [`AuslanderReiten_Cones_TwoConeShiftedMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeShiftedMap.lean), [`AuslanderReiten_Coordinates_TensorFiniteLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteLift.lean), [`AuslanderReiten_Coordinates_TensorNormalizedTop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorNormalizedTop.lean), [`AuslanderReiten_Evaluation_EvaluatedBaseShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedBaseShift.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverInitial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverInitial.lean), [`AuslanderReiten_Evaluation_TensorTwistEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorTwistEvaluation.lean), [`AuslanderReiten_Fibers_ExplicitBimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ExplicitBimoduleFiber.lean), [`AuslanderReiten_Modules_ATwistFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ATwistFunctor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A145`, `OAIQ031A157` and `OAIQ031A158` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A163`, `OAIQ031A164`, `OAIQ031A165`, `OAIQ031A166` and `OAIQ031A167`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A145
import Definitions.Def_OAIQ031A157
import Definitions.Def_OAIQ031A158

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeModuleTriangles
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n))

variable (τ : FrobeniusTrace k R)

variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

def baseSuccessorShiftIso (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf (n + 1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective R (D.term n) := hp n
  exact FiniteLeftModule.projectiveMiddleShiftIso τ
    (M := baseCokernelModule D hf (n + 1)) (N := termModule D hf n)
    (L := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) ((LinearMap.range (D.d n)).mkQ_surjective) (baseStep_exact D hex n)

def baseIteratedShiftIso (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf 0).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((baseCokernelModule D hf n).completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    exact ih ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (n : ℤ)).mapIso
        (baseSuccessorShiftIso D hf τ hex hp n) ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeShiftedMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n))
variable (τ : FrobeniusTrace k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hp : ∀ n, Module.Projective R (D.term n))
variable {U N : FiniteLeftModule k R} (n : ℕ)
variable (e : U.carrier ≃ₗ[R] BaseCokernel D 0)
variable (f : BaseCokernel D n →ₗ[R] N.carrier)

def tailSourceShiftIso :
    (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj
        ((baseCokernelModule D hf n).completeCochain τ))⟦(n : ℤ)⟧ :=
  FiniteLeftModule.resolutionIso τ (M := U) (N := baseCokernelModule D hf 0) e ≪≫
    baseIteratedShiftIso D hf τ hex hp n

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem source_term_finite_k (n : ℕ) :
    Module.Finite k ((sourceData q H).term n) := by
  let := source_finite q H n
  exact Module.Finite.trans Ae _

def sourceAugmentationEquiv :
    (twistedFiniteModule (sourceTwist q H)).carrier ≃ₗ[Ae]
      (TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 0).carrier :=
  (sourceBaseEquiv q H).symm

def sourceFourthToTail :
    (TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4).carrier →ₗ[Ae]
      (firstTailModule q).carrier :=
  (tailMap q H).comp (sourceFourthEquiv q H).symm.toLinearMap

def sourceShiftIso :=
  TwoCone.tailSourceShiftIso (sourceData q H) (source_term_finite_k q H)
    (AEnvelopingFrobeniusTrace k q) (source_exact q H) (source_projective q H)
    (U := twistedFiniteModule (sourceTwist q H)) 4 (sourceAugmentationEquiv q H)

def finiteLift : (twistedFiniteModule (sourceTwist q H)).carrier →ₗ[Ae]
    ((firstTailModule q).canonicalCosyzygies 4).carrier :=
  FiniteLeftModule.shiftedModuleMap (AEnvelopingFrobeniusTrace k q)
    (U := twistedFiniteModule (sourceTwist q H))
    (M := TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4)
    (N := firstTailModule q) 4 (sourceShiftIso q H) (sourceFourthToTail q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ExplicitBimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev fiberTarget : FiniteLeftModule k Ae := (firstTailModule q).canonicalCosyzygies 4

def normalizedLift : (twistedFiniteModule (sourceTwist q H)).carrier ⟶ (fiberTarget q).carrier :=
  ModuleCat.ofHom (X := (twistedFiniteModule (sourceTwist q H)).carrier)
    (Y := (fiberTarget q).carrier) (((H : k)^2)⁻¹ • finiteLift q H)

@[simp] theorem normalizedLift_apply (x : (twistedFiniteModule (sourceTwist q H)).carrier) :
    normalizedLift q H x = ((H : k)^2)⁻¹ • finiteLift q H x := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorNormalizedTop
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def sourceUnit : (twistedFiniteModule (sourceTwist q H)).carrier := ⟨1⟩

attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedBaseShift
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

local instance baseScalar (n : ℕ) : Module k (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).scalar
local instance baseTower (n : ℕ) : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ)
    (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).tower

abbrev evaluatedBaseModule (n : ℕ) :=
  FiniteLeftModule.evaluated X (TwoCone.baseCokernelModule D hf n)

abbrev evaluatedBaseResolution (n : ℕ) := (Q).obj ((evaluatedBaseModule q n).completeCochain τ)

open scoped ModuleCat.Algebra

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverInitial
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]

namespace FiniteLeftModule
variable (τ : FrobeniusTrace k R) (S M : FiniteLeftModule k R)

theorem resolutionSourceAtStableEquiv_lift (e : S.carrier →ₗ[R] M.carrier) :
    resolutionSourceAtStableEquiv τ S M 0
      (CohomologyClass.mk (Cocycle.ofHom (resolutionMap τ e))) =
      StableHom.classOf R _ _ (e.comp (S.completeCochainCokernelEquiv τ).toLinearMap) := by
  rw [resolutionSourceAtStableEquiv_mk]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((S.completeCochain τ).d (-1) 0).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawSourceAt_mk (k := k)]
  have h := LinearMap.congr_fun (resolutionMap_cokernel τ e) (Submodule.Quotient.mk z)
  change Submodule.Quotient.mk (((resolutionMap τ e).f 0).hom z) = _ at h
  change (M.completeCochainCokernelEquiv τ)
    (Submodule.Quotient.mk (((resolutionMap τ e).f 0).hom z)) = _
  rw [h]
  exact (M.completeCochainCokernelEquiv τ).apply_symm_apply _
end FiniteLeftModule

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorTwistEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "X" => A.simpleFiniteModule q

theorem sourceTwist_smul_simple (a : A k q) (x : A.Simple q) :
    sourceTwist q H a • x = a • x := by
  change ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H a) x =
    ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) a x
  induction a using OAI.tensorInductionOn with
  | add a b ha hb =>
    simp only [map_add]
    change (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H a)) x +
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
      (sourceTwist q H b)) x =
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) a) x +
      (ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) b) x
    rw [ha, hb]
  | tmul a b =>
    let y : Resolution.Simple q ⊗[k] Resolution.Simple q := x
    change ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q)
        (sourceTwist q H (a ⊗ₜ[k] b)) y =
      ExternalTensor.representation k R R (Resolution.Simple q) (Resolution.Simple q) (a ⊗ₜ[k] b) y
    induction y using OAI.tensorInductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s t => rfl

theorem sourceInverseTwist_smul_simple (a : A k q) (x : A.Simple q) :
    (sourceTwist q H).symm a • x = a • x := by
  have h := sourceTwist_smul_simple q H ((sourceTwist q H).symm a) x
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

def twistedSimpleEquiv : TwistedLeftModule k (A k q) (sourceTwist q H) (X).carrier ≃ₗ[A k q]
    (X).carrier where
  toFun := TwistedLeftModule.value
  invFun := TwistedLeftModule.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := sourceInverseTwist_smul_simple q H a x.value

def evaluatedTwistEquiv : (FiniteLeftModule.evaluated X (twistedFiniteModule (sourceTwist q H))).carrier ≃ₗ[A k q]
    (X).carrier :=
  (FiniteLeftModule.twistedEvaluationEquiv (sourceTwist q H) X).trans (twistedSimpleEquiv q H)

@[simp] theorem evaluatedTwistEquiv_tmul
    (r : EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)
    (x : (X).carrier) :
    evaluatedTwistEquiv q H (BalancedTensor.tmul r x) = (sourceTwist q H).symm r.value.value • x := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_ATwistFunctor
attribute [-instance] _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

abbrev aInverseRestriction := ExternalTensor.tensorRestriction k (ArExplicit.T k q) (ArExplicit.T k q)
  (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm

instance aInverseRestriction_isEquivalence : (aInverseRestriction q H).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr (TrivialExtension.twist H).symm
      (TrivialExtension.twist H).symm).toRingEquiv

def aInverseEndpoint : A.Simple q ≅ (aInverseRestriction q H).obj (A.Simple q) :=
  ModuleBar.tensorEndpointIso k (ArExplicit.T k q) (ArExplicit.T k q) (Simple q) (Simple q)
    (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseEndpoint_apply (x : A.Simple q) : (aInverseEndpoint q H).hom.hom x = x := by
  exact (ModuleBar.tensorEndpointIso_apply k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) x).trans (by simp; rfl)

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))] in
theorem aInverseTwist_standard (n : ℕ) (x : ASelfExt q n) :
    type_of% (ModuleBar.tensorTwist_eq_exactFunctor k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n x) :=
  ModuleBar.tensorTwist_eq_exactFunctor k (ArExplicit.T k q) (ArExplicit.T k q)
    (Simple q) (Simple q) (TrivialExtension.twist H).symm (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (ArExplicit.T.inverseTwist_simple_compatible q H)
    (ArExplicit.T.inverseTwist_simple_compatible q H) n x

theorem aInverseTwist_standard_scalar (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)
    (n : ℕ) (x : ASelfExt q (3*n)) :
    selfExtIso (k := k) (aInverseEndpoint q H).symm (3*n)
      (x.mapExactFunctor (aInverseRestriction q H)) = (((H⁻¹ : kˣ) : k)^n) • x := by
  rw [selfExtIso_apply]
  exact (aInverseTwist_standard q H (3*n) x).symm.trans
    (aInverseTwistExt_scalar q H hq hq1 hp n x)

end ArExplicit.Resolution

end

end OAI
end


