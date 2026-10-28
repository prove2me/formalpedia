-- Prove2me | Definitions.Def_OAIQ031A162
-- name    : OAIQ031A162
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:01:56.994235+00:00
-- url     : https://prove2.me/theorems/6769cf15-13e3-45e9-88d0-f0a09da94bce
-- title:
--   Definitions bundle OAIQ031A162 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 9 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.T.ordinaryFirstHom`, `OAI.ArExplicit.T.ordinarySecondHom`, `OAI.ArExplicit.TwoCone.evaluatedCompleteComparison`, `OAI.ArExplicit.TwoCone.evaluatedFirstBaseMap`, `OAI.ArExplicit.TwoCone.evaluatedQuotientCocycle`, `OAI.ArExplicit.TwoCone.evaluatedSecondBaseMap`, `OAI.ArExplicit.TwoCone.middleStepInclusion`, `OAI.ArExplicit.TwoCone.middleTermModule`, `OAI.ArExplicit.TwoCone.singletonCoverLift`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeBoundaryIdentification`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeBoundaryIdentification.lean), [`AuslanderReiten_Cones_TwoConeExtensionDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeExtensionDiagrams.lean), [`AuslanderReiten_Coordinates_TensorFiniteLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteLift.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluatedBase`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluatedBase.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverComparison.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverInitial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverInitial.lean), [`AuslanderReiten_Evaluation_EvaluatedQuotientCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedQuotientCubic.lean), [`AuslanderReiten_Resolutions_CubicCoverSquares`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CubicCoverSquares.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A137` and `OAIQ031A157` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A165`, `OAIQ031A166` and `OAIQ031A167`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A137
import Definitions.Def_OAIQ031A157

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeExtensionDiagrams
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

def middleStepInclusion (n : ℕ) :
    (BaseCokernel D (n + 3) × BaseCokernel D (n + 3)) →ₗ[R] middleTerm D n :=
  (baseStepInclusion D hex (n + 2)).prodMap (baseStepInclusion D hex (n + 2))

def singletonCoverLift (n : ℕ) : middleTerm D n →ₗ[R] SkeletonCokernel D n :=
  (LinearMap.range (skeletonD D n)).mkQ.comp (LinearMap.inr R (D.term n) (middleTerm D n))

theorem singletonCoverLift_projection (n : ℕ) :
    (singletonCokernelProjection D n).comp (singletonCoverLift D n) =
      ((LinearMap.range (D.d (n + 2))).mkQ).prodMap ((LinearMap.range (D.d (n + 2))).mkQ) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeBoundaryIdentification
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

abbrev middleTermModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (middleTerm D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf (n + 2); infer_instance

theorem middleStepInclusion_injective (n : ℕ) : Function.Injective (middleStepInclusion D hex n) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  exact Prod.ext ((baseStepInclusion_injective D hex (n + 2)) (congrArg Prod.fst h))
    ((baseStepInclusion_injective D hex (n + 2)) (congrArg Prod.snd h))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteLift
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

theorem firstTailModule_left_projective :
    Module.Projective (A k q)
      ((ModuleCat.restrictScalars (tensorLeftInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_left_projective q

theorem firstTailModule_left_finite :
    Module.Finite (A k q)
      ((ModuleCat.restrictScalars (tensorLeftInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_left_finite q

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CubicCoverSquares
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
universe u
variable {R : Type u} [Ring R] (D : Data R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))

theorem firstCokernelMap_cover (n : ℕ) :
    (D.first n).comp (baseStepInclusion D hex (n+3)) =
      (baseStepInclusion D hex n).comp (firstCokernelMap D (n+1)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (LinearMap.range (D.d (n+4))).mkQ_surjective z
  exact (DFunLike.congr_fun (D.first_comm n) z).symm

theorem firstCokernelMap_quotient (n : ℕ) :
    ((LinearMap.range (D.d n)).mkQ).comp (D.first n) =
      (firstCokernelMap D n).comp (LinearMap.range (D.d (n+3))).mkQ := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedQuotientCubic
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R)

def evaluatedFirstBaseMap (n : ℕ) :
    evaluatedRawTerm D hf X (n+3) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.first n)

def evaluatedSecondBaseMap (n : ℕ) :
    evaluatedRawTerm D hf X (n+3) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.second n)

omit [Module.Finite k R] in
theorem evaluatedFirstBaseMap_quotient (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedFirstBaseMap D hf X n) =
      (FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (firstCokernelMap D n)).comp (evaluatedBaseQuotient D hf X (n+3)) := by
  dsimp only [evaluatedBaseQuotient, evaluatedFirstBaseMap]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    firstCokernelMap_quotient D n]

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluatedBase
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "D" => bimoduleTwoConeData q

def ordinaryFirstHom (n : ℕ) : (D).term (n+3) ⟶ (D).term n :=
  ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) ((D).first n)

def ordinarySecondHom (n : ℕ) : (D).term (n+3) ⟶ (D).term n :=
  ConcreteCategory.ofHom (C := ModuleCat (A₀ ⊗[k] A₀ᵐᵒᵖ)) ((D).second n)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverComparison
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R)
variable (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
local notation "K" => FiniteLeftModule.completeCochain τ S
local notation "P" => evaluatedOrdinaryResolution D hf X hex hr hp
local notation "Q" => completeExtResolution (TotallyAcyclicCochain.to_chain (FiniteLeftModule.completeCochain_totallyAcyclic τ S))

def evaluatedCompleteComparison : EvaluatedCompleteComparison D hf X hex hr hp τ S e where
  hom := ProjectiveResolution.lift
    (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap)) Q P
  hom_f_zero_comp_π_f_zero := by
    erw [ChainComplex.single₀_map_f_zero]
    exact ProjectiveResolution.lift_commutes_zero
      (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap)) Q P

variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)

theorem evaluatedComparisonCokernel_inclusion (n : ℕ) :
    (evaluatedBaseInclusion D hf hex X n).comp
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      (rawCokernelAtInclusion K (n : ℤ)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((K).d (-(((n+1 : ℕ) : ℤ)+1)) (-((n+1 : ℕ) : ℤ))).hom) z
  change (evaluatedBaseInclusion D hf hex X n)
    (evaluatedBaseQuotient D hf X (n+1) (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1) z)) = _
  rw [← LinearMap.comp_apply, ← evaluatedBaseDifferential_factor D hf hex X n]
  exact LinearMap.congr_fun (evaluatedComparisonTerm_comm D hf X hex hr hp τ S e φ n) z

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverInitial
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

namespace TwoCone
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R) (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)
local notation "K" => FiniteLeftModule.completeCochain τ S

omit [CharP k 2] in
theorem evaluatedComparisonCokernel_zero :
    evaluatedComparisonCokernel D hf X hex hr hp τ S e φ 0 =
      e.comp (S.completeCochainCokernelEquiv τ).toLinearMap := by
  have h := φ.hom_f_zero_comp_π_f_zero
  erw [ChainComplex.single₀_map_f_zero] at h
  change φ.hom.f 0 ≫ (evaluatedOrdinaryAugmentation D hf X).f 0 =
    (nonnegativeTailAugmentation (chainOfCochain K)).f 0 ≫
      ModuleCat.ofHom (e.comp (S.fullCokernelEquiv τ).toLinearMap) at h
  rw [evaluatedOrdinaryAugmentation_zero, nonnegativeTailAugmentation_f_zero] at h
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((K).d (-1) 0).hom) z
  have hh := congrArg (fun f => f.hom ((tailTermIso K 0).inv.hom z)) h
  change evaluatedBaseQuotient D hf X 0
    ((φ.hom.f 0).hom ((tailTermIso K 0).inv.hom z)) =
      e ((S.fullCokernelEquiv τ) (Submodule.Quotient.mk ((tailTermIso K 0).inv.hom z))) at hh
  change evaluatedBaseQuotient D hf X 0
    ((φ.hom.f 0).hom ((tailTermIso K 0).inv.hom z)) = _
  rw [hh]
  apply congrArg e
  change (S.completeCochainCokernelEquiv τ)
    (Submodule.Quotient.mk ((tailTermIso K 0).hom.hom ((tailTermIso K 0).inv.hom z))) =
      (S.completeCochainCokernelEquiv τ) (Submodule.Quotient.mk z)
  rw [show (tailTermIso K 0).hom.hom ((tailTermIso K 0).inv.hom z) = z from
    ModuleCat.hom_inv_apply (tailTermIso K 0) z]

end TwoCone
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverCoordinates
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R) (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)

def evaluatedQuotientCocycle (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    (evaluatedOrdinaryComplex D hf X).X (n+1) ⟶ S.carrier :=
  ModuleCat.ofHom (b.comp (evaluatedBaseQuotient D hf X (n+1)))

omit [CharP k 2] [Module.Finite k R] in
theorem evaluatedQuotientCocycle_closed (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    (evaluatedOrdinaryComplex D hf X).d (n+2) (n+1) ≫
      evaluatedQuotientCocycle D hf X S n b = 0 := by
  rw [evaluatedOrdinaryComplex_d]
  apply ModuleCat.hom_ext
  change (b.comp (evaluatedBaseQuotient D hf X (n+1))).comp
    (evaluatedBaseDifferential D hf X (n+1)) = 0
  rw [LinearMap.comp_assoc, evaluatedBaseQuotient_comp_d_zero, LinearMap.comp_zero]

end ArExplicit.TwoCone

end

end OAI
end


