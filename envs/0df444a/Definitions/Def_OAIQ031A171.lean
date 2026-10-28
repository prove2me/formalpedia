-- Prove2me | Definitions.Def_OAIQ031A171
-- name    : OAIQ031A171
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:34:50.222497+00:00
-- url     : https://prove2.me/theorems/36be5fef-91d1-453e-8e36-1ab40019dfd6
-- title:
--   Definitions bundle OAIQ031A171 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 7 definitions and 15 theorems. The definitions and types are `OAI.ArExplicit.T.evaluatedAdjacentMap`, `OAI.ArExplicit.T.evaluatedSingletonHomEquiv`, `OAI.ArExplicit.T.fiberComplete`, `OAI.ArExplicit.T.simpleHomotopyObject`, `OAI.ArExplicit.TwoCone.evaluatedMiddleSuccessorIso`, `OAI.ArExplicit.TwoCone.middleProjection`, `OAI.ArExplicit.TwoCone.middleTermProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ConcreteNativeBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteNativeBar.lean), [`AuslanderReiten_Cones_TwoConeEvaluatedBoundary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeEvaluatedBoundary.lean), [`AuslanderReiten_Coordinates_ConcreteCubicAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteCubicAction.lean), [`AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedConnectingCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleNaturality.lean), [`AuslanderReiten_Evaluation_EvaluatedMiddleShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedMiddleShift.lean), [`AuslanderReiten_Evaluation_EvaluatedTopConnecting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedTopConnecting.lean), [`AuslanderReiten_Evaluation_EvaluatedTopCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedTopCoordinates.lean), [`AuslanderReiten_Fibers_FiberFullHomCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberFullHomCoordinates.lean), [`AuslanderReiten_Modules_ATwistedCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ATwistedCompleteAction.lean), [`AuslanderReiten_Resolutions_SimpleCoverCubicConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/SimpleCoverCubicConjugate.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A163`, `OAIQ031A165` and `OAIQ031A166` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A175`, `OAIQ031A176`, `OAIQ031A177` and `OAIQ031A178`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A163
import Definitions.Def_OAIQ031A165
import Definitions.Def_OAIQ031A166

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

def evaluatedMiddleSuccessorIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj
      ((X.evaluated (middleCokernelModule D hf n)).completeCochain τ) ≅
    ((HomotopyCategory.quotient _ _).obj
      ((X.evaluated (middleCokernelModule D hf (n + 1))).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := middle_right D hf hr n
  letI := hp (n + 2)
  exact FiniteLeftModule.evaluationSuccessorIso X
    (M := middleCokernelModule D hf (n + 1)) (N := middleTermModule D hf n)
    (P := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n)
    (middleStep_exact D hex n) τ

theorem evaluatedSkeletonConnecting_eq (n : ℕ) :
    (evaluatedSkeletonTriangle D hf hex hr X τ n).mor₃ =
      (evaluatedMiddleSuccessorIso D hf hex hr hp X τ n).hom ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ
            (FiniteLeftModule.evaluationMap X
              (M := middleCokernelModule D hf (n + 1)) (N := baseCokernelModule D hf n)
              (rowCokernelMap D n)))) := by
  let := middle_right D hf hr n
  let := hp (n + 2)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := middleCokernelModule D hf (n + 1)) (N₁ := middleTermModule D hf n)
    (P₁ := middleCokernelModule D hf n)
    (M₂ := baseCokernelModule D hf n) (N₂ := skeletonCokernelModule D hf n)
    (P₂ := middleCokernelModule D hf n)
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (bottomCokernelInclusion D n) (singletonCokernelProjection D n)
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n) (middleStep_exact D hex n)
    (bottomCokernelInclusion_injective D hex n) (singletonCokernelProjection_surjective D n)
    (skeletonCokernel_exact D n)
    (rowCokernelMap D n) (singletonCoverLift D n) LinearMap.id
    (singletonCoverLift_boundary D hex n)
    (by simpa only [LinearMap.id_comp, middleCoverQuotient] using singletonCoverLift_projection D n)
  erw [FiniteLeftModule.evaluationMap_id,
    FiniteLeftModule.resolutionMap_id τ (M := X.evaluated (middleCokernelModule D hf n)),
    Category.id_comp] at h
  dsimp only [evaluatedSkeletonTriangle, evaluatedMiddleSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteNativeBar
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "T₀" => T k q
local notation "A₀" => A k q
local notation "S" => Resolution.Simple q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q

theorem simpleCoefficientNative_second (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier).map (ordinarySecondHom q n) ≫
      ((simpleCoefficientComplexIso q).hom.f n ≫
        (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) =
    ((simpleCoefficientComplexIso q).hom.f (n+3) ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f (n+3)) ≫
        simpleNativeSecond q n := by
  exact compose_native_squares
    (simpleCoefficientComplexIso_comparison q (n+3) n (ordinarySecondHom q n))
    (ExternalBalanced.nativeTotalBarIso_second k T₀ T₀ S S (CocycleData.p q) n)

theorem simpleNativeBarIso_second (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D hf X n) ≫
      (simpleNativeBarIso q).hom.f n =
    (simpleNativeBarIso q).hom.f (n+3) ≫ simpleNativeSecond q n := by
  rw [simpleNativeBarIso_hom_f, simpleNativeBarIso_hom_f]
  exact compose_native_squares (simpleOrdinaryBarIso_second q n)
    (simpleCoefficientNative_second q n)

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
local notation "R" => A k q
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "SX" => evaluatedSimpleObject q

def evaluatedSingletonHomEquiv (n : ℕ) (a : ℤ) :
    (SX ⟶ (evaluatedSingletonResolution q n)⟦a⟧) ≃ₗ[k]
      ((SX ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧) ×
       (SX ⟶ (evaluatedBaseResolution q (n+2))⟦a⟧)) :=
  (Linear.homCongr k (Iso.refl _) ((CategoryTheory.shiftFunctor HC a).mapIso
    (evaluatedSingletonProductIso q n))).trans
      (mappedBiproductHomEquiv k (CategoryTheory.shiftFunctor HC a) SX
        (evaluatedBaseResolution q (n+2)) (evaluatedBaseResolution q (n+2)))

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
local notation "R₀" => A k q
abbrev simpleHomotopyObject_p0 :=
  (HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)).obj (A.simpleComplete q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedMiddleNaturality
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)

def middleProjection (first : Bool) (n : ℕ) :
    (middleCokernelModule D hf n).carrier →ₗ[R ⊗[k] Rᵐᵒᵖ]
      (baseCokernelModule D hf (n+2)).carrier :=
  if first then LinearMap.fst _ _ _ else LinearMap.snd _ _ _

def middleTermProjection (first : Bool) (n : ℕ) :
    (middleTermModule D hf n).carrier →ₗ[R ⊗[k] Rᵐᵒᵖ]
      (termModule D hf (n+2)).carrier :=
  if first then LinearMap.fst _ _ _ else LinearMap.snd _ _ _

omit [Module.Finite k R] in
theorem middleProjection_cover (first : Bool) (n : ℕ) :
    (middleTermProjection D hf first n).comp (middleStepInclusion D hex n) =
      (baseStepInclusion D hex (n+2)).comp (middleProjection D hf first (n+1)) := by
  cases first <;> rfl

omit [Module.Finite k R] in
theorem middleProjection_quotient (first : Bool) (n : ℕ) :
    ((LinearMap.range (D.d (n+2))).mkQ).comp (middleTermProjection D hf first n) =
      (middleProjection D hf first n).comp (middleCoverQuotient D n) := by
  cases first <;> rfl

theorem evaluatedMiddleProjection_step (first : Bool) (n : ℕ) :
    (Q).map (FiniteLeftModule.resolutionMap τ
      (FiniteLeftModule.evaluationMap X (middleProjection D hf first n))) ≫
        (evaluatedBaseSuccessorIso D hf hex hr hp X τ (n+2)).hom =
    (evaluatedMiddleSuccessorIso D hf hex hr hp X τ n).hom ≫
      (CategoryTheory.shiftFunctor HC (1 : ℤ)).map
        ((Q).map (FiniteLeftModule.resolutionMap τ
          (FiniteLeftModule.evaluationMap X (middleProjection D hf first (n+1))))) := by
  let := hr (n+2)
  let : Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R
      (middleCokernelModule D hf n).carrier) :=
    EnvelopingBimodule.prod_right_projective
      (baseCokernelModule D hf (n+2)).carrier (baseCokernelModule D hf (n+2)).carrier
  let := hp (n+2)
  have h := FiniteLeftModule.evaluationConnecting_natural X τ
    (M₁ := middleCokernelModule D hf (n+1)) (N₁ := middleTermModule D hf n)
    (P₁ := middleCokernelModule D hf n)
    (M₂ := baseCokernelModule D hf (n+3)) (N₂ := termModule D hf (n+2))
    (P₂ := baseCokernelModule D hf (n+2))
    (middleStepInclusion D hex n) (middleCoverQuotient D n)
    (baseStepInclusion D hex (n+2)) (LinearMap.range (D.d (n+2))).mkQ
    (middleStepInclusion_injective D hex n) (middleCoverQuotient_surjective D n)
    (middleStep_exact D hex n)
    (baseStepInclusion_injective D hex (n+2)) (Submodule.mkQ_surjective _) (baseStep_exact D hex (n+2))
    (middleProjection D hf first (n+1)) (middleTermProjection D hf first n)
    (middleProjection D hf first n)
    (middleProjection_cover D hf hex first n) (middleProjection_quotient D hf first n)
  dsimp only [evaluatedBaseSuccessorIso, evaluatedMiddleSuccessorIso]
  erw [FiniteLeftModule.evaluationSuccessorIso_hom,
    FiniteLeftModule.evaluationSuccessorIso_hom]
  exact h

end ArExplicit.TwoCone

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

local instance middleCoordinateBaseScalarP31 (n : ℕ) : Module k (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).scalar
local instance middleCoordinateBaseTowerP31 (n : ℕ) : IsScalarTower k (R₀ ⊗[k] R₀ᵐᵒᵖ)
    (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).tower
local instance middleCoordinateScalarP31 (n : ℕ) : Module k (TwoCone.middleCokernelModule D hf n).carrier :=
  (TwoCone.middleCokernelModule D hf n).scalar
local instance middleCoordinateTowerP31 (n : ℕ) : IsScalarTower k (R₀ ⊗[k] R₀ᵐᵒᵖ)
    (TwoCone.middleCokernelModule D hf n).carrier :=
  (TwoCone.middleCokernelModule D hf n).tower

theorem evaluatedSingletonFst_eq (n : ℕ) :
    evaluatedSingletonFst q n = FiniteLeftModule.evaluationMap X
      (TwoCone.middleProjection D hf true n) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  rfl

theorem evaluatedSingletonSnd_eq (n : ℕ) :
    evaluatedSingletonSnd q n = FiniteLeftModule.evaluationMap X
      (TwoCone.middleProjection D hf false n) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem resolutionRow
    {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
    (tau : FrobeniusTrace k R) {M N P : FiniteLeftModule k R}
    (a b : M.carrier →ₗ[R] N.carrier) (f g : N.carrier →ₗ[R] P.carrier)
    (row : M.carrier →ₗ[R] P.carrier) (h : row = f.comp a + g.comp b) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau row) =
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau a) ≫
        (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau f) +
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau b) ≫
        (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau g) := by
  rw [h, FiniteLeftModule.resolutionMap_add,
    FiniteLeftModule.resolutionMap_comp, FiniteLeftModule.resolutionMap_comp]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTopCoordinates
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
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q

theorem evaluatedTopAdjacent (n : ℕ) :
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
      (N := TwoCone.middleCokernelModule D₀ hf₀ n)
      (TwoCone.singletonCokernelProjection D₀ n)).comp
      (FiniteLeftModule.evaluationMap X₀
        (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
        (N := TwoCone.skeletonCokernelModule D₀ hf₀ n)
        (-(TwoCone.topAttachingCokernel D₀ n))) =
    FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
      (N := TwoCone.middleCokernelModule D₀ hf₀ n)
      (-(TwoCone.columnCokernelMap D₀ n)) := by
  rw [← FiniteLeftModule.evaluationMap_comp, LinearMap.comp_neg,
    TwoCone.topAttachingCokernel_adjacent]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTopConnecting
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
universe u v

theorem resolutionComposite
    {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
    (tau : FrobeniusTrace k R) {M N P : FiniteLeftModule k R}
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] P.carrier)
    (h : M.carrier →ₗ[R] P.carrier) (he : g.comp f = h) :
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau f) ≫
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau g) =
    (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap tau h) := by
  rw [← FiniteLeftModule.resolutionMap_comp, he]

variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

def evaluatedAdjacentMap (n : ℕ) :=
  FiniteLeftModule.evaluationMap X₀
    (M := TwoCone.baseCokernelModule D₀ hf₀ (n+5))
    (N := TwoCone.middleCokernelModule D₀ hf₀ n) (-(TwoCone.columnCokernelMap D₀ n))

theorem simpleSkeletonTriangle_second (n : ℕ) :
    (simpleSkeletonTriangle q n).mor₂ =
      (Q₀).map (FiniteLeftModule.resolutionMap τ₀
        (FiniteLeftModule.evaluationMap X₀
          (M := TwoCone.skeletonCokernelModule D₀ hf₀ n)
          (N := TwoCone.middleCokernelModule D₀ hf₀ n)
          (TwoCone.singletonCokernelProjection D₀ n))) := by
  exact TwoCone.evaluatedSkeletonTriangle_second D₀ hf₀ (bimodule_exact q)
    (baseTail_right_projective q) X₀ τ₀ n

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberFullHomCoordinates
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "τ₀" => AFrobeniusTrace k q

abbrev fiberComplete := (evaluatedFiber q H₁ H₂).completeCochain τ₀

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

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))]
  [HasDerivedCategory (ModuleCat (A k q))] in
theorem completeTwistIn_quotient :
    (HomotopyCategory.quotient _ _).map (completeTwistIn q H) =
      (BalancedTensor.completeTensorIso (AFrobeniusTrace k q)
        (A.simpleFiniteModule q) (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)).inv :=
  BalancedTensor.completeActionIn_quotient (AFrobeniusTrace k q)
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_SimpleCoverCubicConjugate
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem firstCoverConjugateStart :
    type_of% (ModuleBar.resolutionExt_nativeFirst k T₀ T₀ S₀ S₀
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (simpleOrdinaryResolution q)
      (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)) :=
  ModuleBar.resolutionExt_nativeFirst k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (simpleOrdinaryResolution q)
    (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)

theorem secondCoverConjugateStart :
    type_of% (ModuleBar.resolutionExt_nativeSecond k T₀ T₀ S₀ S₀
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (simpleOrdinaryResolution q)
      (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)) :=
  ModuleBar.resolutionExt_nativeSecond k T₀ T₀ S₀ S₀
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (simpleOrdinaryResolution q)
    (evaluatedBaseZeroEquiv q).toModuleIso (nativeToCanonicalSimple q)

end ArExplicit.T

end

end OAI
end


