-- Prove2me | Definitions.Def_OAIQ031A166
-- name    : OAIQ031A166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:14:16.118785+00:00
-- url     : https://prove2.me/theorems/18fb0028-e250-4fa6-9074-528fa3f58ca9
-- title:
--   Definitions bundle OAIQ031A166 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.ArExplicit.T.completeTwistIn`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ConcreteNativeBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteNativeBar.lean), [`AuslanderReiten_Cones_TwoConeExtensionDiagrams`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeExtensionDiagrams.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluatedBase`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluatedBase.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluationCoefficient.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverCanonical.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverCoordinates.lean), [`AuslanderReiten_Evaluation_EvaluatedCoverInitial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCoverInitial.lean), [`AuslanderReiten_Evaluation_EvaluatedOrdinaryFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedOrdinaryFunctor.lean), [`AuslanderReiten_Modules_ATwistedCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ATwistedCompleteAction.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A159`, `OAIQ031A160`, `OAIQ031A161` and `OAIQ031A162` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A171` and `OAIQ031A172`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A159
import Definitions.Def_OAIQ031A160
import Definitions.Def_OAIQ031A161
import Definitions.Def_OAIQ031A162

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

theorem singletonCoverLift_boundary (n : ℕ) :
    (singletonCoverLift D n).comp (middleStepInclusion D hex n) =
      (bottomCokernelInclusion D n).comp (rowCokernelMap D n) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  obtain ⟨x, rfl⟩ := (LinearMap.range (D.d (n + 3))).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (LinearMap.range (D.d (n + 3))).mkQ_surjective y
  change Submodule.Quotient.mk (0, (D.d (n + 2) x, D.d (n + 2) y)) =
    Submodule.Quotient.mk (D.first n x + D.second n y, (0, 0))
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨(0, (-x, -y)), ?_⟩
  simp [skeletonD, middleD, attachingRow, coneBlock_apply]
  abel

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedOrdinaryFunctor
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
variable (X : FiniteLeftModule k R)
variable (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)
variable (e : ∀ n, D.term n ≅ P.X n)
local notation "E" => EnvelopingBimodule.evaluationFunctor k R X.carrier

omit [Module.Finite k R] in
theorem evaluatedOrdinaryFunctorIso_comparison
    (he : ∀ n, (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom)
    (m n : ℕ) (d : D.term m ⟶ D.term n) (p : P.X m ⟶ P.X n)
    (hd : d ≫ (e n).hom = (e m).hom ≫ p) :
    (E).map d ≫ (evaluatedOrdinaryFunctorIso D hf X P e he).hom.f n =
      (evaluatedOrdinaryFunctorIso D hf X P e he).hom.f m ≫ (E).map p := by
  have h := congrArg (E).map hd
  rw [(E).map_comp, (E).map_comp] at h
  exact h

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluatedBase
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
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "X" => A.simpleFiniteModule q
local notation "E" => simpleEvaluationFunctor q

theorem simpleOrdinaryBarIso_first (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D hf X n) ≫
      (simpleOrdinaryBarIso q).hom.f n =
    (simpleOrdinaryBarIso q).hom.f (n+3) ≫
      (E).map (ordinaryFirstHom q n) := by
  exact TwoCone.evaluatedOrdinaryFunctorIso_comparison D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q) (n+3) n
    (ordinaryFirstHom q n) (ordinaryFirstHom q n) (by
      dsimp only [ordinaryBarTermIso, Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id])

theorem simpleOrdinaryBarIso_second (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedSecondBaseMap D hf X n) ≫
      (simpleOrdinaryBarIso q).hom.f n =
    (simpleOrdinaryBarIso q).hom.f (n+3) ≫
      (E).map (ordinarySecondHom q n) := by
  exact TwoCone.evaluatedOrdinaryFunctorIso_comparison D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q) (n+3) n
    (ordinarySecondHom q n) (ordinarySecondHom q n) (by
      dsimp only [ordinaryBarTermIso, Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id])

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient
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
local notation "A₀" => A k q

attribute [local instance] OAI.ArExplicit.T.canonicalSimpleScalar
attribute [local instance] OAI.ArExplicit.T.canonicalSimpleTower
theorem simpleCoefficientComplexIso_comparison (m n : ℕ)
    (f : (shuffledBarComplex q).X m ⟶ (shuffledBarComplex q).X n) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (A.simpleFiniteModule q).carrier).map f ≫
        (simpleCoefficientComplexIso q).hom.f n =
      (simpleCoefficientComplexIso q).hom.f m ≫
        (EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)).map f :=
  EnvelopingBimodule.coefficientComplexIso_comparison k A₀
    (nativeToCanonicalSimple q) (shuffledBarComplex q) m n f

end ArExplicit.T

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

theorem simpleCoefficientNative_first (n : ℕ) :
    (EnvelopingBimodule.evaluationFunctor k A₀ (X).carrier).map (ordinaryFirstHom q n) ≫
      ((simpleCoefficientComplexIso q).hom.f n ≫
        (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) =
    ((simpleCoefficientComplexIso q).hom.f (n+3) ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f (n+3)) ≫
        simpleNativeFirst q n := by
  exact compose_native_squares
    (simpleCoefficientComplexIso_comparison q (n+3) n (ordinaryFirstHom q n))
    (ExternalBalanced.nativeTotalBarIso_first k T₀ T₀ S S (CocycleData.p q) n)

theorem simpleNativeBarIso_first (n : ℕ) :
    ModuleCat.ofHom (TwoCone.evaluatedFirstBaseMap D hf X n) ≫
      (simpleNativeBarIso q).hom.f n =
    (simpleNativeBarIso q).hom.f (n+3) ≫ simpleNativeFirst q n := by
  rw [simpleNativeBarIso_hom_f, simpleNativeBarIso_hom_f]
  exact compose_native_squares (simpleOrdinaryBarIso_first q n)
    (simpleCoefficientNative_first q n)

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

theorem evaluatedComparison_initial :
    FiniteLeftModule.HasSourceCoordinates τ S (X.evaluated (baseCokernelModule D hf 0)) 0
      (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e)))
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ 0) := by
  change FiniteLeftModule.resolutionSourceAtStableEquiv _ _ _ _ _ = _
  rw [FiniteLeftModule.resolutionSourceAtStableEquiv_lift,
    evaluatedComparisonCokernel_zero]
  rfl
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

theorem evaluatedCover_source (n : ℕ) :
    FiniteLeftModule.HasSourceCoordinates τ S (X.evaluated (baseCokernelModule D hf n)) (n : ℤ)
      ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
        (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) n)
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ n) := by
  apply FiniteCoverTower.coverClassFrom_source τ (evaluatedCoverTower D hf X hex hr hp) S
    (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e)))
    (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ)
    (evaluatedComparisonTerm D hf X hex hr hp τ S e φ)
  · exact evaluatedComparison_initial D hf X hex hr hp τ S e φ
  · intro j
    apply LinearMap.ext
    intro z
    rfl
  · intro j
    exact evaluatedComparisonCokernel_inclusion D hf X hex hr hp τ S e φ j

include φ in

theorem evaluatedCover_ext (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    FiniteLeftModule.fullPositiveModuleExtEquiv τ S n
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ b) ((n+1 : ℕ) : ℤ)
        ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
          (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) (n+1))) =
      (Ext.mk₀ (ModuleCat.ofHom e)).comp
        ((evaluatedOrdinaryResolution D hf X hex hr hp).extMk
          (evaluatedQuotientCocycle D hf X S n b) (n+2) rfl
          (evaluatedQuotientCocycle_closed D hf X S n b)) (zero_add _) := by
  apply FiniteLeftModule.fullPositiveModuleExtEquiv_eq_precomp_extMk τ S
    (X.evaluated (baseCokernelModule D hf 0)).carrier (ModuleCat.ofHom e)
    (evaluatedOrdinaryResolution D hf X hex hr hp) φ n
    (evaluatedQuotientCocycle D hf X S n b) (evaluatedQuotientCocycle_closed D hf X S n b)
    _ (b.comp (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)))
  · erw [FiniteLeftModule.resolutionSourceAtStableEquiv_postcomp]
    erw [show FiniteLeftModule.resolutionSourceAtStableEquiv τ S
        (X.evaluated (baseCokernelModule D hf (n+1))) ((n+1 : ℕ) : ℤ) _ =
        StableHom.classOf R _ _ (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ (n+1)) from
      evaluatedCover_source D hf X hex hr hp τ S e φ (n+1), StableHom.postcomp_classOf]
  · intro z
    rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCoverCanonical
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
theorem evaluatedCover_ext_canonical (n : ℕ)
    (b : (X.evaluated (baseCokernelModule D hf (n+1))).carrier →ₗ[R] S.carrier) :
    FiniteLeftModule.fullPositiveModuleExtEquiv τ S n
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ b) ((n+1 : ℕ) : ℤ)
        ((evaluatedCoverTower D hf X hex hr hp).coverClassFrom τ S
          (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e))) (n+1))) =
      (Ext.mk₀ (ModuleCat.ofHom e)).comp
        ((evaluatedOrdinaryResolution D hf X hex hr hp).extMk
          (evaluatedQuotientCocycle D hf X S n b) (n+2) rfl
          (evaluatedQuotientCocycle_closed D hf X S n b)) (zero_add _) :=
  evaluatedCover_ext D hf X hex hr hp τ S e
    (evaluatedCompleteComparison D hf X hex hr hp τ S e) n b

end ArExplicit.TwoCone

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

abbrev completeTwistIn := BalancedTensor.completeActionIn (AFrobeniusTrace k q)
  (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

end ArExplicit.T

end

end OAI
end


