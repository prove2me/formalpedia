-- Prove2me | Definitions.Def_OAIQ031A161
-- name    : OAIQ031A161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:01:49.587102+00:00
-- url     : https://prove2.me/theorems/d5b5d037-7d91-41ea-a184-976f52fd78bc
-- title:
--   Definitions bundle OAIQ031A161 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 11 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.TwoCone.columnCokernelMap`, `OAI.ArExplicit.TwoCone.evaluatedBase`, `OAI.ArExplicit.TwoCone.evaluatedBaseIteration`, `OAI.ArExplicit.TwoCone.evaluatedBaseSuccessorIso`, `OAI.ArExplicit.TwoCone.evaluatedCoverTower`, `OAI.ArExplicit.TwoCone.evaluatedFirstCokernel`, `OAI.ArExplicit.TwoCone.evaluatedSecondCokernel`, `OAI.ArExplicit.TwoCone.middleCoverQuotient`, `OAI.ArExplicit.TwoCone.rowCokernelMap`, `OAI.ArExplicit.TwoCone.skeletonCokernelModule`, `OAI.ArExplicit.TwoCone.topCoverLift`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeBoundaryIdentification`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeBoundaryIdentification.lean), [`AuslanderReiten_Cones_TwoConeConnectingMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeConnectingMaps.lean), [`AuslanderReiten_Cones_TwoConeEvaluatedBoundary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeEvaluatedBoundary.lean), [`AuslanderReiten_Cones_TwoConeExtensionDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeExtensionDiagrams.lean), [`AuslanderReiten_Cones_TwoConeModuleTriangles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeModuleTriangles.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_TensorTopCoverSquares`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopCoverSquares.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverProducts.lean), [`AuslanderReiten_Evaluation_EvaluatedCubicCover`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCubicCover.lean), [`AuslanderReiten_Resolutions_CubicCoverSquares`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CubicCoverSquares.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A145` and `OAIQ031A157` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A165`, `OAIQ031A166` and `OAIQ031A167`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A145
import Definitions.Def_OAIQ031A157

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

theorem bottomCokernelInclusion_injective
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Injective (bottomCokernelInclusion D n) :=
  ConeCokernel.inclusion_injective _ _ _ (middleD D (n + 1)) (attachingRow D (n + 1))
    (middleD_exact D hex n) (attachingRow_comm D n)

theorem singletonCokernelProjection_surjective (n : ℕ) :
    Function.Surjective (singletonCokernelProjection D n) :=
  (middleCokernelEquiv D n).surjective.comp (ConeCokernel.projection_surjective _ _ _)

theorem skeletonCokernel_exact (n : ℕ) :
    Function.Exact (bottomCokernelInclusion D n) (singletonCokernelProjection D n) := by
  intro x
  change middleCokernelEquiv D n
    (ConeCokernel.projection (D.d n) (middleD D n) (attachingRow D n) x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact ConeCokernel.exact _ _ _ x

theorem topCokernel_exact (n : ℕ) :
    Function.Exact (skeletonCokernelInclusion D n) (topCokernelProjection D n) := by
  intro x
  change negativeTopCokernelEquiv D n
    (ConeCokernel.projection (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)
      (skeletonCokernelCoordinates D n x)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (ConeCokernel.exact (skeletonD D n) (-(D.d (n + 4)))
      (topAttaching D n) (skeletonCokernelCoordinates D n x)).mp h
    refine ⟨y, ?_⟩
    change (skeletonCokernelCoordinates D n).symm
      (ConeCokernel.inclusion (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n) y) = x
    rw [hy, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy⟩
    apply (ConeCokernel.exact _ _ _ _).mpr
    refine ⟨y, ?_⟩
    rw [← hy]
    exact ((skeletonCokernelCoordinates D n).apply_symm_apply _).symm

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeConnectingMaps
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

def rowCokernelMap (n : ℕ) : (BaseCokernel D (n + 3) × BaseCokernel D (n + 3)) →ₗ[R]
    BaseCokernel D n :=
  (firstCokernelMap D n).coprod (secondCokernelMap D n)

def columnCokernelMap (n : ℕ) : BaseCokernel D (n + 5) →ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  (secondCokernelMap D (n + 2)).prod (-(firstCokernelMap D (n + 2)))

theorem topAttachingCokernel_adjacent (n : ℕ) :
    (singletonCokernelProjection D n).comp (topAttachingCokernel D n) = columnCokernelMap D n := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 5))).mkQ_surjective x
  change (Submodule.Quotient.mk (D.second (n + 2) x),
      Submodule.Quotient.mk (-D.first (n + 2) x)) =
    (Submodule.Quotient.mk (D.second (n + 2) x), -Submodule.Quotient.mk (D.first (n + 2) x))
  rw [Submodule.Quotient.mk_neg]

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeModuleTriangles
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev skeletonCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (SkeletonCokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    infer_instance

end ArExplicit.TwoCone

end

end OAI
end

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

def topCoverLift (n : ℕ) : D.term (n + 4) →ₗ[R] Cokernel D n :=
  (LinearMap.range (d D n)).mkQ.comp
    (((0 : D.term (n + 4) →ₗ[R] D.term n).prod 0).prod
      ((0 : D.term (n + 4) →ₗ[R] D.term (n + 2)).prod LinearMap.id))

theorem topCoverLift_projection (n : ℕ) :
    (topCokernelProjection D n).comp (topCoverLift D n) = (LinearMap.range (D.d (n + 4))).mkQ := by
  apply LinearMap.ext
  intro x
  rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeBoundaryIdentification
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def middleCoverQuotient (n : ℕ) : middleTerm D n →ₗ[R]
    (BaseCokernel D (n + 2) × BaseCokernel D (n + 2)) :=
  ((LinearMap.range (D.d (n + 2))).mkQ).prodMap ((LinearMap.range (D.d (n + 2))).mkQ)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeEvaluatedBoundary
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.TwoCone
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

def evaluatedBaseSuccessorIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj
      ((X.evaluated (baseCokernelModule D hf n)).completeCochain τ) ≅
    ((HomotopyCategory.quotient _ _).obj
      ((X.evaluated (baseCokernelModule D hf (n + 1))).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := hr n
  letI := hp n
  exact FiniteLeftModule.evaluationSuccessorIso X
    (M := baseCokernelModule D hf (n + 1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _)
    (baseStep_exact D hex n) τ

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopCoverSquares
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "D" => bimoduleTwoConeData q
local notation "Q" => sourceData q H

theorem topCover_left (n : ℕ) :
    (bimoduleTopComparison q H n).comp
      (TwoCone.baseStepInclusion Q (source_exact q H) n) =
    (TwoCone.baseStepInclusion D (bimodule_exact q) (n+1)).comp
      (bimoduleTopCokernel q H (n+1)) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [LinearMap.comp_apply, TwoCone.baseStepInclusion_mk, bimoduleTopCokernel_mk]
    exact (LinearMap.congr_fun (bimoduleTopComparison_chain q H n) x).symm

theorem topCover_right (n : ℕ) :
    ((LinearMap.range ((D).d (n+1))).mkQ).comp (bimoduleTopComparison q H n) =
      (bimoduleTopCokernel q H n).comp ((LinearMap.range ((Q).d n)).mkQ) := by
  apply LinearMap.ext
  intro x
  rfl

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

theorem secondCokernelMap_cover (n : ℕ) :
    (D.second n).comp (baseStepInclusion D hex (n+3)) =
      (baseStepInclusion D hex n).comp (secondCokernelMap D (n+1)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (LinearMap.range (D.d (n+4))).mkQ_surjective z
  exact (DFunLike.congr_fun (D.second_comm n) z).symm

theorem secondCokernelMap_quotient (n : ℕ) :
    ((LinearMap.range (D.d n)).mkQ).comp (D.second n) =
      (secondCokernelMap D n).comp (LinearMap.range (D.d (n+3))).mkQ := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCubicCover
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
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

abbrev evaluatedBase (n : ℕ) := (Q).obj
  ((X.evaluated (baseCokernelModule D hf n)).completeCochain τ)

def evaluatedFirstCokernel (n : ℕ) :
    evaluatedBase D hf X τ (n+3) ⟶ evaluatedBase D hf X τ n :=
  (Q).map (FiniteLeftModule.resolutionMap τ
    (FiniteLeftModule.evaluationMap X
      (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
      (firstCokernelMap D n)))

def evaluatedSecondCokernel (n : ℕ) :
    evaluatedBase D hf X τ (n+3) ⟶ evaluatedBase D hf X τ n :=
  (Q).map (FiniteLeftModule.resolutionMap τ
    (FiniteLeftModule.evaluationMap X
      (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
      (secondCokernelMap D n)))

theorem evaluatedSecondCokernel_step (n : ℕ) :
    evaluatedSecondCokernel D hf X τ n ≫
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ n).hom =
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+3)).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        (evaluatedSecondCokernel D hf X τ (n+1)) := by
  let := hr n
  let := hr (n+3)
  let := hp n
  let := hp (n+3)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := baseCokernelModule D hf (n+4)) (N₁ := termModule D hf (n+3))
    (P₁ := baseCokernelModule D hf (n+3))
    (M₂ := baseCokernelModule D hf (n+1)) (N₂ := termModule D hf n)
    (P₂ := baseCokernelModule D hf n)
    (baseStepInclusion D hex (n+3)) (LinearMap.range (D.d (n+3))).mkQ
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex (n+3)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n+3))
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _) (baseStep_exact D hex n)
    (secondCokernelMap D (n+1)) (D.second n) (secondCokernelMap D n)
    (secondCokernelMap_cover D hex n) (secondCokernelMap_quotient D n)
  simp only [evaluatedSecondCokernel, evaluatedBaseSuccessorIso,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

def evaluatedBaseIteration (n : ℕ) : evaluatedBase D hf X τ 0 ≅
    (evaluatedBase D hf X τ n)⟦(n : ℤ)⟧ :=
  iteratedShiftIso (evaluatedBase D hf X τ)
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ) n

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverProducts
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def evaluatedCoverTower : FiniteCoverTower (k := k) (R := R) where
  obj n := X.evaluated (baseCokernelModule D hf n)
  middle n := X.evaluated (termModule D hf n)
  inclusion n := evaluatedBaseInclusion D hf hex X n
  quotient n := evaluatedBaseQuotient D hf X n
  injective n := (evaluatedBaseCover_exact D hf hex hr X n).1
  surjective n := (evaluatedBaseCover_exact D hf hex hr X n).2.1
  exact n := (evaluatedBaseCover_exact D hf hex hr X n).2.2
  projective n := by
    let := hp n
    exact FiniteLeftModule.evaluated_projective X (M := termModule D hf n)

theorem evaluatedCoverTower_coverClassFrom_hom (S : FiniteLeftModule k R)
    (f : S.completeCochain τ ⟶
      (X.evaluated (baseCokernelModule D hf 0)).completeCochain τ) (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ)
      ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
        (CohomologyClass.mk (Cocycle.ofHom f)) n) =
      (HomotopyCategory.quotient _ _).map f ≫
        (evaluatedBaseIteration D hf hex hr hp X τ n).hom :=
  FiniteCoverTower.coverClassFrom_hom τ (evaluatedCoverTower D hf X hex hr hp) S f n

end ArExplicit.TwoCone

end

end OAI
end


