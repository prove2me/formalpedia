-- Prove2me | Definitions.Def_OAIQ031A157
-- name    : OAIQ031A157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:57:29.160427+00:00
-- url     : https://prove2.me/theorems/2d7deedc-6708-4efb-84bd-43aab80e431f
-- title:
--   Definitions bundle OAIQ031A157 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 18 definitions and 23 theorems. The definitions and types are `OAI.ArExplicit.T.firstTailModule`, `OAI.ArExplicit.TwoCone.EvaluatedCompleteComparison`, `OAI.ArExplicit.TwoCone.baseCokernelModule`, `OAI.ArExplicit.TwoCone.baseStepInclusion`, `OAI.ArExplicit.TwoCone.cokernelModule`, `OAI.ArExplicit.TwoCone.evaluatedBaseDifferential`, `OAI.ArExplicit.TwoCone.evaluatedBaseInclusion`, `OAI.ArExplicit.TwoCone.evaluatedBaseQuotient`, `OAI.ArExplicit.TwoCone.evaluatedComparisonCokernel`, `OAI.ArExplicit.TwoCone.evaluatedComparisonTerm`, `OAI.ArExplicit.TwoCone.evaluatedOrdinaryAugmentation`, `OAI.ArExplicit.TwoCone.evaluatedOrdinaryComplex`, `OAI.ArExplicit.TwoCone.evaluatedOrdinaryResolution`, `OAI.ArExplicit.TwoCone.evaluatedRawTerm`, `OAI.ArExplicit.TwoCone.firstCokernelMap`, `OAI.ArExplicit.TwoCone.secondCokernelMap`, `OAI.ArExplicit.TwoCone.termModule`, `OAI.ArExplicit.TwoCone.topAttachingCokernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeConnectingMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeConnectingMaps.lean), [`AuslanderReiten_Cones_TwoConeExtensionDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeExtensionDiagrams.lean), [`AuslanderReiten_Cones_TwoConeModuleTriangles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeModuleTriangles.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_TensorFiniteLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteLift.lean), [`AuslanderReiten_Evaluation_EvaluatedBaseQuotient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedBaseQuotient.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverComparison.lean), [`AuslanderReiten_Resolutions_EvaluatedOrdinaryResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/EvaluatedOrdinaryResolution.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A155` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A159`, `OAIQ031A160`, `OAIQ031A161` and `OAIQ031A162`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A155

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

@[simp]
theorem singletonCokernelProjection_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2)) :
    singletonCokernelProjection D n (Submodule.Quotient.mk (a, (b, c))) =
      (Submodule.Quotient.mk b, Submodule.Quotient.mk c) := rfl

@[simp]
theorem skeletonCokernelInclusion_mk (n : ℕ) (a : D.term n) (b c : D.term (n + 2)) :
    skeletonCokernelInclusion D n (Submodule.Quotient.mk (a, (b, c))) =
      Submodule.Quotient.mk ((a, b), (c, 0)) := rfl

theorem topCokernelProjection_surjective (n : ℕ) :
    Function.Surjective (topCokernelProjection D n) :=
  (negativeTopCokernelEquiv D n).surjective.comp
    ((ConeCokernel.projection_surjective _ _ _).comp
      (skeletonCokernelCoordinates D n).surjective)

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

def firstCokernelMap (n : ℕ) : BaseCokernel D (n + 3) →ₗ[R] BaseCokernel D n :=
  (LinearMap.range (D.d (n + 3))).liftQ
    ((LinearMap.range (D.d n)).mkQ.comp (D.first n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨D.first (n + 1) y, DFunLike.congr_fun (D.first_comm n) y⟩)

def secondCokernelMap (n : ℕ) : BaseCokernel D (n + 3) →ₗ[R] BaseCokernel D n :=
  (LinearMap.range (D.d (n + 3))).liftQ
    ((LinearMap.range (D.d n)).mkQ.comp (D.second n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨D.second (n + 1) y, DFunLike.congr_fun (D.second_comm n) y⟩)

@[simp]
theorem firstCokernelMap_mk (n : ℕ) (x : D.term (n + 3)) :
    firstCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.first n x) := rfl

@[simp]
theorem secondCokernelMap_mk (n : ℕ) (x : D.term (n + 3)) :
    secondCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (D.second n x) := rfl

def topAttachingCokernel (n : ℕ) : BaseCokernel D (n + 5) →ₗ[R] SkeletonCokernel D n :=
  (LinearMap.range (D.d (n + 5))).liftQ
    ((LinearMap.range (skeletonD D n)).mkQ.comp (topAttaching D n)) (by
      rintro x ⟨y, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨-topAttaching D (n + 1) y, ?_⟩
      have h := DFunLike.congr_fun (topAttaching_comm D n) y
      change skeletonD D n (topAttaching D (n + 1) y) = topAttaching D n (-D.d (n + 5) y) at h
      rw [map_neg] at h
      rw [map_neg, h, neg_neg])

@[simp]
theorem topAttachingCokernel_mk (n : ℕ) (x : D.term (n + 5)) :
    topAttachingCokernel D n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (0, (D.second (n + 2) x, -D.first (n + 2) x)) := rfl

end ArExplicit.TwoCone

end

end OAI
end

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

abbrev termModule (n : ℕ) : FiniteLeftModule k R where
  carrier := D.term n
  scalar := inferInstance
  tower := inferInstance
  finite := hf n

abbrev baseCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BaseCokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf n; infer_instance

abbrev cokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (Cokernel D n)
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    let := hf (n + 4)
    infer_instance

variable (τ : FrobeniusTrace k R)

variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))

def baseStepInclusion (n : ℕ) : BaseCokernel D (n + 1) →ₗ[R] D.term n :=
  (LinearMap.ker (LinearMap.range (D.d n)).mkQ).subtype.comp
    (baseSuccessorEquiv D hex n).toLinearMap

theorem baseStepInclusion_injective (n : ℕ) : Function.Injective (baseStepInclusion D hex n) :=
  Subtype.val_injective.comp (baseSuccessorEquiv D hex n).injective

theorem baseStep_exact (n : ℕ) :
    Function.Exact (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ := by
  intro x
  constructor
  · intro hx
    refine ⟨(baseSuccessorEquiv D hex n).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((baseSuccessorEquiv D hex n).apply_symm_apply ⟨x, hx⟩)
  · rintro ⟨y, rfl⟩
    exact ((baseSuccessorEquiv D hex n) y).property

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

@[simp]
theorem baseStepInclusion_mk (n : ℕ) (x : D.term (n + 1)) :
    baseStepInclusion D hex n (Submodule.Quotient.mk x) = D.d n x := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem bimodule_term_finite_k (n : ℕ) :
    Module.Finite k ((bimoduleTwoConeData q).term n) := by
  let := bimodule_term_finite q n
  exact Module.Finite.trans Ae _

abbrev firstTailModule : FiniteLeftModule k Ae :=
  TwoCone.cokernelModule (bimoduleTwoConeData q) (bimodule_term_finite_k q) 1

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedBaseQuotient
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R)

abbrev evaluatedRawTerm (n : ℕ) := (X.evaluated (termModule D hf n)).carrier

def evaluatedBaseDifferential (n : ℕ) :
    evaluatedRawTerm D hf X (n+1) →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (D.d n)

def evaluatedBaseQuotient (n : ℕ) : evaluatedRawTerm D hf X n →ₗ[R]
    (X.evaluated (baseCokernelModule D hf n)).carrier :=
  FiniteLeftModule.evaluationMap X (LinearMap.range (D.d n)).mkQ

def evaluatedBaseInclusion (n : ℕ) :
    (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] evaluatedRawTerm D hf X n :=
  FiniteLeftModule.evaluationMap X (baseStepInclusion D hex n)

theorem baseDifferential_factor (n : ℕ) :
    (baseStepInclusion D hex n).comp (LinearMap.range (D.d (n+1))).mkQ = D.d n := by
  ext z
  exact baseStepInclusion_mk D hex n z

theorem evaluatedBaseDifferential_factor (n : ℕ) :
    evaluatedBaseDifferential D hf X n =
      (evaluatedBaseInclusion D hf hex X n).comp (evaluatedBaseQuotient D hf X (n+1)) := by
  dsimp only [evaluatedBaseDifferential, evaluatedBaseInclusion, evaluatedBaseQuotient]
  rw [← FiniteLeftModule.evaluationMap_comp, baseDifferential_factor D hex n]

include hr in

theorem evaluatedBaseCover_exact (n : ℕ) :
    Function.Injective (evaluatedBaseInclusion D hf hex X n) ∧
    Function.Surjective (evaluatedBaseQuotient D hf X n) ∧
    Function.Exact (evaluatedBaseInclusion D hf hex X n) (evaluatedBaseQuotient D hf X n) := by
  let := hr n
  have h := FiniteLeftModule.evaluation_shortExact X
    (M := baseCokernelModule D hf (n+1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n)
    (baseStepInclusion D hex n) (LinearMap.range (D.d n)).mkQ
    (baseStepInclusion_injective D hex n) (Submodule.mkQ_surjective _) (baseStep_exact D hex n)
  exact h

include hex hr in

theorem evaluatedBase_range_eq_ker (n : ℕ) :
    LinearMap.range (evaluatedBaseDifferential D hf X n) =
      LinearMap.ker (evaluatedBaseQuotient D hf X n) := by
  have he := (evaluatedBaseCover_exact D hf hex hr X n).2.2
  have hs := (evaluatedBaseCover_exact D hf hex hr X (n+1)).2.1
  rw [evaluatedBaseDifferential_factor D hf hex X n]
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact (he _).2 ⟨evaluatedBaseQuotient D hf X (n+1) w,rfl⟩
  · intro hz
    obtain ⟨w,hw⟩ := (he z).1 hz
    obtain ⟨v,rfl⟩ := hs w
    exact ⟨v,hw⟩

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_EvaluatedOrdinaryResolution
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)

theorem evaluatedBaseDifferential_square (n : ℕ) :
    (evaluatedBaseDifferential D hf X n).comp (evaluatedBaseDifferential D hf X (n+1)) = 0 := by
  dsimp only [evaluatedBaseDifferential]
  rw [← FiniteLeftModule.evaluationMap_comp, D.square]
  exact evaluation_zero X

def evaluatedOrdinaryComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (evaluatedRawTerm D hf X)
    (fun n => ModuleCat.ofHom (evaluatedBaseDifferential D hf X n))
    (fun n => ModuleCat.hom_ext (evaluatedBaseDifferential_square D hf X n))

@[simp] theorem evaluatedOrdinaryComplex_d (n : ℕ) :
    (evaluatedOrdinaryComplex D hf X).d (n+1) n =
      ModuleCat.ofHom (evaluatedBaseDifferential D hf X n) := by
  simp only [evaluatedOrdinaryComplex, ChainComplex.of.d]
  apply Category.id_comp

variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))

include hex hr in
theorem evaluatedBaseDifferential_ker (n : ℕ) :
    LinearMap.ker (evaluatedBaseDifferential D hf X n) =
      LinearMap.ker (evaluatedBaseQuotient D hf X (n+1)) := by
  rw [evaluatedBaseDifferential_factor D hf hex X n]
  ext z
  change evaluatedBaseInclusion D hf hex X n (evaluatedBaseQuotient D hf X (n+1) z) = 0 ↔ _
  have hi := (evaluatedBaseCover_exact D hf hex hr X n).1
  constructor
  · intro h
    apply hi
    simpa using h
  · intro h
    rw [show evaluatedBaseQuotient D hf X (n+1) z = 0 from h, map_zero]

include hex hr in
theorem evaluatedOrdinaryComplex_exact (n : ℕ) :
    (evaluatedOrdinaryComplex D hf X).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((evaluatedOrdinaryComplex D hf X).d (n+2) (n+1)).hom =
    LinearMap.ker ((evaluatedOrdinaryComplex D hf X).d (n+1) n).hom
  rw [evaluatedOrdinaryComplex_d, evaluatedOrdinaryComplex_d]
  exact (evaluatedBase_range_eq_ker D hf hex hr X (n+1)).trans
    (evaluatedBaseDifferential_ker D hf X hex hr n).symm

theorem evaluatedBaseQuotient_comp_d_zero (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedBaseDifferential D hf X n) = 0 := by
  have h : ((LinearMap.range (D.d n)).mkQ).comp (D.d n) = 0 := by
    ext y
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,rfl⟩
  have he := congrArg (fun f => FiniteLeftModule.evaluationMap X
    (M := termModule D hf (n+1)) (N := baseCokernelModule D hf n) f) h
  erw [FiniteLeftModule.evaluationMap_comp X
    (M := termModule D hf (n+1)) (N := termModule D hf n)
    (P := baseCokernelModule D hf n) (D.d n) (LinearMap.range (D.d n)).mkQ,
    evaluation_zero X (M := termModule D hf (n+1)) (N := baseCokernelModule D hf n)] at he
  exact he

def evaluatedOrdinaryAugmentation : evaluatedOrdinaryComplex D hf X ⟶
    (ChainComplex.single₀ (ModuleCat.{u} R)).obj (X.evaluated (baseCokernelModule D hf 0)).carrier :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0), by
      rw [evaluatedOrdinaryComplex_d]
      exact ModuleCat.hom_ext (evaluatedBaseQuotient_comp_d_zero D hf X 0)⟩

theorem evaluatedOrdinaryAugmentation_zero : (evaluatedOrdinaryAugmentation D hf X).f 0 =
    ModuleCat.ofHom (evaluatedBaseQuotient D hf X 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))

def evaluatedOrdinaryResolution :
    ProjectiveResolution (X.evaluated (baseCokernelModule D hf 0)).carrier where
  complex := evaluatedOrdinaryComplex D hf X
  projective n := by
    let := hp n
    let := FiniteLeftModule.evaluated_projective X (M := termModule D hf n)
    change CategoryTheory.Projective (evaluatedRawTerm D hf X n)
    infer_instance
  π := evaluatedOrdinaryAugmentation D hf X
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((evaluatedOrdinaryComplex D hf X).d 1 0).hom =
            LinearMap.ker ((evaluatedOrdinaryAugmentation D hf X).f 0).hom
          rw [evaluatedOrdinaryComplex_d, evaluatedOrdinaryAugmentation_zero]
          exact evaluatedBase_range_eq_ker D hf hex hr X 0
        · rw [ModuleCat.epi_iff_surjective]
          exact (evaluatedBaseCover_exact D hf hex hr X 0).2.1
      · exact (evaluatedOrdinaryComplex D hf X).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact evaluatedOrdinaryComplex_exact D hf X hex hr n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverComparison
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev EvaluatedCompleteComparison := ProjectiveResolution.Hom Q P
  (ModuleCat.ofHom (e.comp (FiniteLeftModule.fullCokernelEquiv τ S).toLinearMap))

variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)

def evaluatedComparisonTerm (n : ℕ) : (K).X (-(n : ℤ)) →ₗ[R] evaluatedRawTerm D hf X n :=
  (φ.hom.f n).hom.comp (tailTermIso K n).inv.hom

theorem evaluatedComparisonTerm_comm (n : ℕ) :
    (evaluatedBaseDifferential D hf X n).comp
      (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      ((K).d (-((n+1 : ℕ) : ℤ)) (-(n : ℤ))).hom := by
  have h := φ.hom.comm (n+1) n
  change φ.hom.f (n+1) ≫ (evaluatedOrdinaryComplex D hf X).d (n+1) n =
    (nonnegativeTail (chainOfCochain K)).d (n+1) n ≫ φ.hom.f n at h
  rw [evaluatedOrdinaryComplex_d, tailTerm_d K (n+1) n rfl] at h
  have hh := congrArg (fun f => (tailTermIso K (n+1)).inv ≫ f) h
  erw [Category.assoc, Iso.inv_hom_id_assoc] at hh
  exact congrArg ModuleCat.Hom.hom hh

theorem evaluatedComparisonTerm_closed (n : ℕ) :
    ((evaluatedBaseQuotient D hf X n).comp (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n)).comp
      ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom = 0 := by
  have hc := evaluatedComparisonTerm_comm D hf X hex hr hp τ S e φ n
  change (evaluatedBaseDifferential D hf X n).comp
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ (n+1)) =
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n).comp
      ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom at hc
  rw [LinearMap.comp_assoc, ← hc,
    ← LinearMap.comp_assoc, evaluatedBaseQuotient_comp_d_zero, LinearMap.zero_comp]

def evaluatedComparisonCokernel (n : ℕ) : RawCokernelAt K (n : ℤ) →ₗ[R]
    (X.evaluated (baseCokernelModule D hf n)).carrier :=
  (LinearMap.range ((K).d (-((n : ℤ)+1)) (-(n : ℤ))).hom).liftQ
    ((evaluatedBaseQuotient D hf X n).comp (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n))
    (LinearMap.range_le_ker_iff.mpr (evaluatedComparisonTerm_closed D hf X hex hr hp τ S e φ n))

@[simp]
theorem evaluatedComparisonCokernel_mk (n : ℕ) (z : (K).X (-(n : ℤ))) :
    evaluatedComparisonCokernel D hf X hex hr hp τ S e φ n (Submodule.Quotient.mk z) =
      evaluatedBaseQuotient D hf X n (evaluatedComparisonTerm D hf X hex hr hp τ S e φ n z) := rfl

end ArExplicit.TwoCone

end

end OAI
end


