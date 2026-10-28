-- Prove2me | Definitions.Def_OAIQ031A160
-- name    : OAIQ031A160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:05:58.100642+00:00
-- url     : https://prove2.me/theorems/56a42f6d-e951-474b-bc2b-92e539b343c9
-- title:
--   Definitions bundle OAIQ031A160 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 14 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.T.nativeToCanonicalSimple`, `OAI.ArExplicit.T.ordinaryBarTermIso`, `OAI.ArExplicit.T.simpleCoefficientComplexIso`, `OAI.ArExplicit.T.simpleEvaluationFunctor`, `OAI.ArExplicit.T.simpleNativeBarIso`, `OAI.ArExplicit.T.simpleOrdinaryBarIso`, `OAI.ArExplicit.T.simpleOrdinaryResolution`, `OAI.ArExplicit.TwoCone.baseResolution`, `OAI.ArExplicit.TwoCone.coneTailData`, `OAI.ArExplicit.TwoCone.coneTermModule`, `OAI.ArExplicit.TwoCone.evaluatedOrdinaryFunctorIso`, `OAI.ArExplicit.TwoCone.evaluatedOrdinaryTermIso`, `OAI.ArExplicit.TwoCone.evaluatedResolutionTermIso`, `OAI.ArExplicit.TwoCone.middleCokernelModule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ConcreteBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteBarFreeAugmentation.lean), [`AuslanderReiten_Bar_ConcreteNativeBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ConcreteNativeBar.lean), [`AuslanderReiten_Cones_ConcreteTwoConeEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeEvaluation.lean), [`AuslanderReiten_Cones_TwoConeIteration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeIteration.lean), [`AuslanderReiten_Cones_TwoConeModuleTriangles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeModuleTriangles.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Cones_TwoConeStableRepresentative`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeStableRepresentative.lean), [`AuslanderReiten_Coordinates_TensorFiniteLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorFiniteLift.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluatedBase`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluatedBase.lean), [`AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteEvaluationCoefficient.lean), [`AuslanderReiten_Evaluation_EvaluatedOrdinaryFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedOrdinaryFunctor.lean), [`AuslanderReiten_Resolutions_EvaluatedResolutionTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/EvaluatedResolutionTerms.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A126`, `OAIQ031A136` and `OAIQ031A157` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A163`, `OAIQ031A164`, `OAIQ031A165`, `OAIQ031A166` and `OAIQ031A167`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A126
import Definitions.Def_OAIQ031A136
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

theorem negativeD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (-(D.d (n + 1))) (-(D.d n)) := by
  intro x
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hex n x).mp (neg_eq_zero.mp h)
    exact ⟨-y, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    apply neg_eq_zero.mpr
    exact (hex n x).mpr ⟨-y, by simpa using hy⟩

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeModuleTriangles
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev middleCokernelModule (n : ℕ) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BaseCokernel D (n + 2) × BaseCokernel D (n + 2))
  scalar := inferInstance
  tower := inferInstance
  finite := by let := hf (n + 2); infer_instance

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorFiniteLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem firstTailModule_right_projective :
    Module.Projective (A k q)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (tensorRightInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_right_projective q

theorem firstTailModule_right_finite :
    Module.Finite (A k q)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (tensorRightInclusion k (A k q) (A k q)ᵐᵒᵖ)).obj
        (firstTailModule q).carrier) := firstTail_right_finite q

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeEvaluation
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "A₀" => A k q
local notation "D" => bimoduleTwoConeData q

theorem baseTail_right_projective (n : ℕ) : Module.Projective A₀ᵐᵒᵖ
    (EnvelopingBimodule k A₀ (TwoCone.baseCokernelModule D (bimodule_term_finite_k q) n).carrier) := by
  let j := tensorRightInclusion k A₀ A₀ᵐᵒᵖ
  let : Module.Projective A₀ᵐᵒᵖ (TwoCone.BaseCokernel ((bimoduleTwoConeData q).restrict j) 0) :=
    Module.Projective.of_equiv (baseRightEquiv q).symm
  let : Module.Projective A₀ᵐᵒᵖ (TwoCone.BaseCokernel ((bimoduleTwoConeData q).restrict j) n) :=
    TwoCone.baseCokernel_projective ((bimoduleTwoConeData q).restrict j)
      (TwoCone.restricted_exact j D (bimodule_exact q)) (baseTerm_right_projective q) n
  let e := (EnvelopingBimodule.rightEquiv
    (TwoCone.baseCokernelModule D (bimodule_term_finite_k q) n).carrier).trans
      (TwoCone.baseCokernelRestrictionEquiv j D n)
  exact Module.Projective.of_equiv e.symm

end T
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedOrdinaryFunctor
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def evaluatedOrdinaryTermIso (n : ℕ) : evaluatedRawTerm D hf X n ≅ (E).obj (P.X n) :=
  (E).mapIso (e n)

omit [Module.Finite k R] in
theorem evaluatedOrdinaryTermIso_square (n : ℕ)
    (he : (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom) :
    (evaluatedOrdinaryTermIso D hf X P e (n+1)).hom ≫ (E).map (P.d (n+1) n) =
      ModuleCat.ofHom (evaluatedBaseDifferential D hf X n) ≫
        (evaluatedOrdinaryTermIso D hf X P e n).hom := by
  have h := congrArg (E).map he
  rw [(E).map_comp, (E).map_comp] at h
  exact h

def evaluatedOrdinaryFunctorIso
    (he : ∀ n, (e (n+1)).hom ≫ P.d (n+1) n = ModuleCat.ofHom (D.d n) ≫ (e n).hom) :
    evaluatedOrdinaryComplex D hf X ≅ ((E).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (evaluatedOrdinaryTermIso D hf X P e)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [evaluatedOrdinaryComplex_d]
      exact evaluatedOrdinaryTermIso_square D hf X P e j (he j))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluatedBase
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
abbrev simpleEvaluationFunctor := EnvelopingBimodule.evaluationFunctor k (A k q) (A.simpleFiniteModule q).carrier
local notation "E" => simpleEvaluationFunctor q

abbrev simpleOrdinaryResolution :=
  TwoCone.evaluatedOrdinaryResolution D hf X (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q)

def ordinaryBarTermIso (n : ℕ) : (D).term n ≅ (shuffledBarComplex q).X n := Iso.refl _

theorem ordinaryBarTermIso_d (n : ℕ) :
    (ordinaryBarTermIso q (n+1)).hom ≫ (shuffledBarComplex q).d (n+1) n =
      ModuleCat.ofHom ((D).d n) ≫ (ordinaryBarTermIso q n).hom := by
  dsimp only [ordinaryBarTermIso, Iso.refl_hom]
  erw [Category.id_comp]

def simpleOrdinaryBarIso : (simpleOrdinaryResolution q).complex ≅
    ((E).mapHomologicalComplex (ComplexShape.down ℕ)).obj (shuffledBarComplex q) :=
  TwoCone.evaluatedOrdinaryFunctorIso D hf X (shuffledBarComplex q)
    (ordinaryBarTermIso q) (ordinaryBarTermIso_d q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteEvaluationCoefficient
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def nativeToCanonicalSimple : (A.simpleFiniteModule q).carrier ≅ canonicalTensorSimple q :=
  (ExternalTensor.canonicalTensorIso k T₀ T₀ S S).symm

attribute [local instance] OAI.ArExplicit.T.canonicalSimpleScalar
attribute [local instance] OAI.ArExplicit.T.canonicalSimpleTower
def simpleCoefficientComplexIso :
    ((EnvelopingBimodule.evaluationFunctor k A₀ (A.simpleFiniteModule q).carrier).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (shuffledBarComplex q) ≅
    ((EnvelopingBimodule.evaluationFunctor k A₀ (canonicalTensorSimple q)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (shuffledBarComplex q) :=
  EnvelopingBimodule.coefficientComplexIso k A₀ (nativeToCanonicalSimple q) (shuffledBarComplex q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteNativeBar
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "S" => Resolution.Simple q

def simpleNativeBarIso : (simpleOrdinaryResolution q).complex ≅
    ExternalTensor.complex k T₀ T₀ (ModuleBar.complex k T₀ S) (ModuleBar.complex k T₀ S) :=
  simpleOrdinaryBarIso q ≪≫ simpleCoefficientComplexIso q ≪≫
    ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S

theorem simpleNativeBarIso_hom :
    (simpleNativeBarIso q).hom =
      (simpleOrdinaryBarIso q).hom ≫
        (simpleCoefficientComplexIso q ≪≫
          ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom := rfl

theorem simpleCoefficientNativeIso_hom :
    (simpleCoefficientComplexIso q ≪≫
      ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom =
    (simpleCoefficientComplexIso q).hom ≫
      (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom := rfl

/-- The degreewise map of the native comparison is the composite of its three factors. -/
theorem simpleNativeBarIso_hom_f (n : ℕ) :
    (simpleNativeBarIso q).hom.f n =
      (simpleOrdinaryBarIso q).hom.f n ≫
        ((simpleCoefficientComplexIso q).hom.f n ≫
          (ExternalBalanced.nativeTotalBarIso k T₀ T₀ S S).hom.f n) := by
  rw [simpleNativeBarIso_hom, simpleCoefficientNativeIso_hom,
    HomologicalComplex.comp_f]
  erw [HomologicalComplex.comp_f]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ConcreteBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

omit [CharP k 2] in
theorem barCyclicCover_eq_augmentation :
    ExternalTensor.barCyclicCover k (T k q) (T k q)
      (Resolution.Simple q) (Resolution.Simple q)
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq) =
      ModuleCat.ofHom (A.augmentation q) ≫ (nativeToCanonicalSimple q).hom := by
  have h := ExternalTensor.barCyclicCover_eq k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
  rw [tensorCyclicCover_eq_augmentation q hq] at h
  exact h

theorem simpleBarFreeCoordinate_augmentation :
    simpleBarFreeCoordinate q hq ≫ ModuleCat.ofHom (A.augmentation q) ≫
      (nativeToCanonicalSimple q).hom =
      (ExternalTensor.augmentation k (T k q) (T k q)
        (ModuleBar.nativeResolution k (T k q) (Resolution.Simple q))
        (ModuleBar.nativeResolution k (T k q) (Resolution.Simple q))).f 0 := by
  have h := ExternalTensor.barTotalFreeCoordinate_augmentation k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
  rw [barCyclicCover_eq_augmentation q hq] at h
  exact h

end ArExplicit.T

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

abbrev baseResolution (n : ℕ) :=
  (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
    ((baseCokernelModule D hf n).completeCochain τ)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeStableRepresentative
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (hp : ∀ n, Module.Projective R (D.term n))

def coneTailData : Data R where
  term := term D
  d := d D
  first _ := 0
  second _ := 0
  square := d_square D
  first_comm _ := by simp
  second_comm _ := by simp
  comparisons_comm _ := by simp

abbrev coneTermModule (n : ℕ) : FiniteLeftModule k R where
  carrier := term D n
  scalar := inferInstance
  tower := inferInstance
  finite := by
    let := hf n
    let := hf (n + 2)
    let := hf (n + 4)
    infer_instance

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_EvaluatedResolutionTerms
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))

def evaluatedResolutionTermIso (n : ℕ) :
    (evaluatedOrdinaryResolution D hf X hex hr hp).complex.X n ≅ evaluatedRawTerm D hf X n :=
  Iso.refl _

@[simp] theorem evaluatedResolutionTermIso_inv_apply (n : ℕ) (x : evaluatedRawTerm D hf X n) :
    (evaluatedResolutionTermIso D hf X hex hr hp n).inv x = x := rfl

end ArExplicit.TwoCone

end

end OAI
end


