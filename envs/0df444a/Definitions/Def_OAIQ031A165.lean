-- Prove2me | Definitions.Def_OAIQ031A165
-- name    : OAIQ031A165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:23:35.006027+00:00
-- url     : https://prove2.me/theorems/d5673a2e-ab46-4266-bca5-4f5c16991511
-- title:
--   Definitions bundle OAIQ031A165 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 9 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.T.completeTwistOut`, `OAI.ArExplicit.T.evaluatedTwistFunctor`, `OAI.ArExplicit.T.finiteLiftClass`, `OAI.ArExplicit.T.simpleHomFiltration`, `OAI.ArExplicit.T.simpleSkeletonTriangle`, `OAI.ArExplicit.T.simpleTopTriangle`, `OAI.ArExplicit.TwoCone.evaluatedHomFiltration`, `OAI.ArExplicit.TwoCone.evaluatedSkeletonTriangle`, `OAI.ArExplicit.TwoCone.evaluatedTopTriangle`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Cones_ConcreteTwoConeEvaluation`, `AuslanderReiten_Cones_TwoConeBoundaryIdentification`, `AuslanderReiten_Cones_TwoConeEvaluatedBoundary`, `AuslanderReiten_Cones_TwoConeEvaluatedTriangles`, `AuslanderReiten_Cones_TwoConeExtensionDiagrams`, `AuslanderReiten_Cones_TwoConeIteration`, `AuslanderReiten_Cones_TwoConeSkeleton`, `AuslanderReiten_Coordinates_TensorFiniteLift`, `AuslanderReiten_Coordinates_TensorFiniteTop`, `AuslanderReiten_Evaluation_EvaluatedCubicCover`, `AuslanderReiten_Evaluation_EvaluatedTriangleArrows`, `AuslanderReiten_Ext_ATwistedTensorExt`, `AuslanderReiten_Modules_ATwistedCompleteAction`.
--
--   **Imports.** It imports the bundles `OAIQ031A159`, `OAIQ031A160`, `OAIQ031A161` and `OAIQ031A162` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A170`, `OAIQ031A171` and `OAIQ031A172`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A159
import Definitions.Def_OAIQ031A160
import Definitions.Def_OAIQ031A161
import Definitions.Def_OAIQ031A162

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

theorem skeletonCokernelInclusion_injective
    (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Injective (skeletonCokernelInclusion D n) :=
  (skeletonCokernelCoordinates D n).symm.injective.comp
    (ConeCokernel.inclusion_injective _ _ _ (-(D.d (n + 5))) (topAttaching D (n + 1))
      (negativeD_exact D hex (n + 4)) (topAttaching_comm D n))

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

theorem topCoverLift_boundary (n : ℕ) :
    (topCoverLift D n).comp (baseStepInclusion D hex (n + 4)) =
      (skeletonCokernelInclusion D n).comp (-(topAttachingCokernel D n)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 5))).mkQ_surjective x
  change Submodule.Quotient.mk ((0, 0), (0, D.d (n + 4) x)) =
    skeletonCokernelInclusion D n (-Submodule.Quotient.mk
      (0, (D.second (n + 2) x, -D.first (n + 2) x)))
  rw [← Submodule.Quotient.mk_neg, skeletonCokernelInclusion_mk]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨((0, 0), (0, x)), ?_⟩
  simp [d, firstD, secondOnFirst, coneBlock_apply]

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

theorem middleCoverQuotient_surjective (n : ℕ) : Function.Surjective (middleCoverQuotient D n) := by
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 2))).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (LinearMap.range (D.d (n + 2))).mkQ_surjective y
  exact ⟨(x, y), rfl⟩

theorem middleStep_exact (n : ℕ) :
    Function.Exact (middleStepInclusion D hex n) (middleCoverQuotient D n) := by
  rintro ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (baseStep_exact D hex (n + 2) x).mp (congrArg Prod.fst h)
    obtain ⟨b, hb⟩ := (baseStep_exact D hex (n + 2) y).mp (congrArg Prod.snd h)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact Prod.ext ((baseStep_exact D hex (n + 2) x).mpr ⟨a, congrArg Prod.fst h⟩)
      ((baseStep_exact D hex (n + 2) y).mpr ⟨b, congrArg Prod.snd h⟩)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeEvaluatedTriangles
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.TwoCone
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

omit [Module.Finite k R] in
include hr in
theorem middle_right_projective (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) := by
  let := hr (n + 2)
  exact EnvelopingBimodule.prod_right_projective
    (baseCokernelModule D hf (n + 2)).carrier (baseCokernelModule D hf (n + 2)).carrier

def evaluatedSkeletonTriangle (n : ℕ) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := middle_right_projective D hf hr n
  exact FiniteLeftModule.evaluationTriangle X
    (M := baseCokernelModule D hf n) (N := skeletonCokernelModule D hf n)
    (P := middleCokernelModule D hf n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n) τ

theorem evaluatedSkeletonTriangle_distinguished (n : ℕ) :
    evaluatedSkeletonTriangle D hf hex hr X τ n ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := middle_right_projective D hf hr n
  exact FiniteLeftModule.evaluationTriangle_distinguished _ _ _ _ _ _ _

def evaluatedTopTriangle (n : ℕ) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := hr (n + 4)
  exact FiniteLeftModule.evaluationTriangle X
    (M := skeletonCokernelModule D hf n) (N := cokernelModule D hf n)
    (P := baseCokernelModule D hf (n + 4))
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n) τ

theorem evaluatedTopTriangle_distinguished (n : ℕ) :
    evaluatedTopTriangle D hf hex hr X τ n ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := hr (n + 4)
  exact FiniteLeftModule.evaluationTriangle_distinguished _ _ _ _ _ _ _

def evaluatedHomFiltration (V : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (n : ℕ) :=
  twoTriangleHomFiltration k V
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₁
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₂
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₃
    (evaluatedTopTriangle D hf hex hr X τ n).mor₁
    (evaluatedTopTriangle D hf hex hr X τ n).mor₂
    (evaluatedTopTriangle D hf hex hr X τ n).mor₃
    (evaluatedSkeletonTriangle_distinguished D hf hex hr X τ n)
    (evaluatedTopTriangle_distinguished D hf hex hr X τ n)

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

include hr in
omit [Module.Finite k R] in
theorem middle_right (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) := by
  let := hr (n + 2)
  exact EnvelopingBimodule.prod_right_projective
    (baseCokernelModule D hf (n + 2)).carrier (baseCokernelModule D hf (n + 2)).carrier

theorem evaluatedTopConnecting_eq (n : ℕ) :
    (evaluatedTopTriangle D hf hex hr X τ n).mor₃ =
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n + 4)).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (FiniteLeftModule.evaluationMap X
              (M := baseCokernelModule D hf (n + 5)) (N := skeletonCokernelModule D hf n)
              (-(topAttachingCokernel D n))))) := by
  let := hr (n + 4)
  let := hp (n + 4)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := baseCokernelModule D hf (n + 5)) (N₁ := termModule D hf (n + 4))
    (P₁ := baseCokernelModule D hf (n + 4))
    (M₂ := skeletonCokernelModule D hf n) (N₂ := cokernelModule D hf n)
    (P₂ := baseCokernelModule D hf (n + 4))
    (baseStepInclusion D hex (n + 4)) (LinearMap.range (D.d (n + 4))).mkQ
    (skeletonCokernelInclusion D n) (topCokernelProjection D n)
    (baseStepInclusion_injective D hex (n + 4)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n + 4))
    (skeletonCokernelInclusion_injective D hex n) (topCokernelProjection_surjective D n)
    (topCokernel_exact D n)
    (-(topAttachingCokernel D n)) (topCoverLift D n) LinearMap.id
    (topCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp] using topCoverLift_projection D n)
  erw [FiniteLeftModule.evaluationMap_id,
    FiniteLeftModule.resolutionMap_id τ (M := X.evaluated (baseCokernelModule D hf (n + 4))),
    Category.id_comp] at h
  dsimp only [evaluatedTopTriangle, evaluatedBaseSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteLift
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def finiteLiftClass :=
  FiniteLeftModule.shiftedResolutionMap (AEnvelopingFrobeniusTrace k q)
    (U := twistedFiniteModule (sourceTwist q H))
    (M := TwoCone.baseCokernelModule (sourceData q H) (source_term_finite_k q H) 4)
    (N := firstTailModule q) 4 (sourceShiftIso q H) (sourceFourthToTail q H)

theorem finiteLift_spec :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap (AEnvelopingFrobeniusTrace k q) (finiteLift q H)) =
        finiteLiftClass q H :=
  FiniteLeftModule.shiftedModuleMap_spec (AEnvelopingFrobeniusTrace k q) 4
    (sourceShiftIso q H) (sourceFourthToTail q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
namespace ArExplicit
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

namespace T
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "D" => bimoduleTwoConeData q

def simpleSkeletonTriangle (n : ℕ) :=
  TwoCone.evaluatedSkeletonTriangle D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

def simpleTopTriangle (n : ℕ) :=
  TwoCone.evaluatedTopTriangle D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q) n

def simpleHomFiltration (n : ℕ) :=
  TwoCone.evaluatedHomFiltration D (bimodule_term_finite_k q) (bimodule_exact q)
    (baseTail_right_projective q) (A.simpleFiniteModule q) (AFrobeniusTrace k q)
    ((HomotopyCategory.quotient _ _).obj ((A.simpleFiniteModule q).completeCochain (AFrobeniusTrace k q))) n

end T
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeIteration
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n)) (τ : FrobeniusTrace k R)
variable (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n))
variable (hp : ∀ n, Module.Projective R (D.term n))

theorem baseIteratedShiftIso_eq_iterated (n : ℕ) :
    baseIteratedShiftIso D hf τ hex hp n =
      iteratedShiftIso (baseResolution D hf τ) (baseSuccessorShiftIso D hf τ hex hp) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [baseIteratedShiftIso, Nat.recAux, iteratedShiftIso] at *
    erw [ih]

end ArExplicit.TwoCone

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

theorem topOneShift_natural (n : ℕ) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
      (M := TwoCone.baseCokernelModule Q hQ n) (N := TwoCone.baseCokernelModule D hD (n+1))
      (bimoduleTopCokernel q H n)) ≫
        (TwoCone.baseSuccessorShiftIso D hD τ (bimodule_exact q) (bimodule_term_projective q) (n+1)).hom =
    (TwoCone.baseSuccessorShiftIso Q hQ τ (source_exact q H) (source_projective q H) n).hom ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} Ae) (ComplexShape.up ℤ)) (1 : ℤ)).map
        ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
          (M := TwoCone.baseCokernelModule Q hQ (n+1)) (N := TwoCone.baseCokernelModule D hD (n+2))
          (bimoduleTopCokernel q H (n+1)))) := by
  have h := FiniteLeftModule.resolutionConnecting_natural τ
    (M₁ := TwoCone.baseCokernelModule Q hQ (n+1)) (N₁ := TwoCone.termModule Q hQ n)
    (L₁ := TwoCone.baseCokernelModule Q hQ n)
    (M₂ := TwoCone.baseCokernelModule D hD (n+2)) (N₂ := TwoCone.termModule D hD (n+1))
    (L₂ := TwoCone.baseCokernelModule D hD (n+1))
    (TwoCone.baseStepInclusion Q (source_exact q H) n) (LinearMap.range ((Q).d n)).mkQ
    (TwoCone.baseStepInclusion D (bimodule_exact q) (n+1)) (LinearMap.range ((D).d (n+1))).mkQ
    (TwoCone.baseStepInclusion_injective Q (source_exact q H) n) (Submodule.mkQ_surjective _)
    (TwoCone.baseStep_exact Q (source_exact q H) n)
    (TwoCone.baseStepInclusion_injective D (bimodule_exact q) (n+1)) (Submodule.mkQ_surjective _)
    (TwoCone.baseStep_exact D (bimodule_exact q) (n+1))
    (bimoduleTopCokernel q H (n+1)) (bimoduleTopComparison q H n) (bimoduleTopCokernel q H n)
    (topCover_left q H n) (topCover_right q H n)
  let := bimodule_term_projective q (n+1)
  let := source_projective q H n
  simpa only [TwoCone.baseSuccessorShiftIso, FiniteLeftModule.projectiveMiddleShiftIso_hom] using h

end ArExplicit.T

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

theorem evaluatedFirstCokernel_step (n : ℕ) :
    evaluatedFirstCokernel D hf X τ n ≫
      (evaluatedBaseSuccessorIso D hf hex hr hp X τ n).hom =
    (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+3)).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        (evaluatedFirstCokernel D hf X τ (n+1)) := by
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
    (firstCokernelMap D (n+1)) (D.first n) (firstCokernelMap D n)
    (firstCokernelMap_cover D hex n) (firstCokernelMap_quotient D n)
  simp only [evaluatedFirstCokernel, evaluatedBaseSuccessorIso,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTriangleArrows
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

namespace TwoCone
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (X : FiniteLeftModule k R) (τ : FrobeniusTrace k R)

theorem evaluatedSkeletonTriangle_second (n : ℕ) :
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₂ =
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
        (FiniteLeftModule.evaluationMap X
          (M := skeletonCokernelModule D hf n) (N := middleCokernelModule D hf n)
          (singletonCokernelProjection D n))) := by
  let := hr (n+2)
  let : Module.Projective Rᵐᵒᵖ
      (EnvelopingBimodule k R (middleCokernelModule D hf n).carrier) :=
    EnvelopingBimodule.prod_right_projective
      (baseCokernelModule D hf (n+2)).carrier (baseCokernelModule D hf (n+2)).carrier
  exact FiniteLeftModule.evaluationTriangle_second X _ _
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n) τ

end TwoCone
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ATwistedTensorExt
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev evaluatedTwistFunctor := BalancedTensor.functor (k := k) (R := A k q) (S := A k q)
  (F := EnvelopingBimodule k (A k q) (twistedFiniteModule (sourceTwist q H)).carrier)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_ATwistedCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev completeTwistOut := BalancedTensor.completeActionOut (AFrobeniusTrace k q)
  (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

end ArExplicit.T

end

end OAI
end


