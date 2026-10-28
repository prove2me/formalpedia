-- Prove2me | Definitions.Def_OAIQ031A167
-- name    : OAIQ031A167
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T16:17:20.605968+00:00
-- url     : https://prove2.me/theorems/f369be31-0526-4ab2-acc5-825e49a42f77
-- title:
--   Definitions bundle OAIQ031A167 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 2 definitions, 4 instances and 6 theorems. The definitions and types are `OAI.ArExplicit.T.evaluatedTwistIso`, `OAI.ArExplicit.T.explicitBimodule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Evaluation_EvaluatedQuotientCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedQuotientCubic.lean), [`AuslanderReiten_Ext_ATwistedTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ATwistedTensorExt.lean), [`AuslanderReiten_Fibers_ExplicitBimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ExplicitBimoduleFiber.lean), [`AuslanderReiten_Fibers_ExplicitBimoduleProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/ExplicitBimoduleProjective.lean), [`AuslanderReiten_Modules_ATwistedCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/ATwistedCompleteAction.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A159`, `OAIQ031A160`, `OAIQ031A161` and `OAIQ031A162` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A172`, `OAIQ031A173`, `OAIQ031A174` and `OAIQ031A177`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A159
import Definitions.Def_OAIQ031A160
import Definitions.Def_OAIQ031A161
import Definitions.Def_OAIQ031A162

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

omit [Module.Finite k R] in
theorem evaluatedSecondBaseMap_quotient (n : ℕ) :
    (evaluatedBaseQuotient D hf X n).comp (evaluatedSecondBaseMap D hf X n) =
      (FiniteLeftModule.evaluationMap X
        (M := baseCokernelModule D hf (n+3)) (N := baseCokernelModule D hf n)
        (secondCokernelMap D n)).comp (evaluatedBaseQuotient D hf X (n+3)) := by
  dsimp only [evaluatedBaseQuotient, evaluatedSecondBaseMap]
  rw [← FiniteLeftModule.evaluationMap_comp, ← FiniteLeftModule.evaluationMap_comp,
    secondCokernelMap_quotient D n]

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ExplicitBimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

abbrev explicitBimodule :=
  BimoduleFiber.bimodule (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂)

theorem explicitBimodule_left :
    Module.Finite R (explicitBimodule q H₁ H₂) ∧
      Module.Projective R (explicitBimodule q H₁ H₂) := by
  let := firstTailModule_left_finite q
  let := firstTailModule_left_projective q
  exact BimoduleFiber.left (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂) (AEnvelopingFrobeniusTrace k q)

theorem explicitBimodule_right :
    Module.Finite Rᵐᵒᵖ (explicitBimodule q H₁ H₂) ∧
      Module.Projective Rᵐᵒᵖ (explicitBimodule q H₁ H₂) := by
  let := firstTailModule_right_finite q
  let := firstTailModule_right_projective q
  exact BimoduleFiber.right (firstTailModule q) (sourceTwist q H₁) (sourceTwist q H₂)
    (normalizedLift q H₁) (normalizedLift q H₂) (AEnvelopingFrobeniusTrace k q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ATwistedTensorExt
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def evaluatedTwistIso :=
  BalancedTensor.nativeEvaluationIso
    (A.simpleFiniteModule q) (evaluatedTwistEquiv q H)

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem inverseEndpoint_inv_apply (x : (Resolution.aInverseRestriction q H).obj (A.Simple q)) :
    (Resolution.aInverseEndpoint q H).inv.hom x = x := by
  have hh := congrArg (fun f => f.hom x) (Resolution.aInverseEndpoint q H).inv_hom_id
  change (Resolution.aInverseEndpoint q H).hom.hom
    ((Resolution.aInverseEndpoint q H).inv.hom x) = x at hh
  rw [Resolution.aInverseEndpoint_apply] at hh
  exact hh

omit [CharP k 2] [HasDerivedCategory (ModuleCat (T k q))] in
theorem evaluatedTwistEndpoint_eq :
    type_of% (twistedFiniteEndpoint_symm_eq (sourceTwist q H) (A.simpleFiniteModule q)
      (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
      (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)) :=
  twistedFiniteEndpoint_symm_eq (sourceTwist q H) (A.simpleFiniteModule q)
    (evaluatedTwistEquiv q H) (Resolution.aInverseEndpoint q H)
    (fun a x => (inverseEndpoint_inv_apply q H _).trans (evaluatedTwistEquiv_tmul q H a x).symm)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_ExplicitBimoduleProjective
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.Resolution.aInverseRestriction_isEquivalence _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.twistedEnvelopingFunctor_equivalence _root_.OAI.ArExplicit.twistedEnveloping_left_finite _root_.OAI.ArExplicit.twistedEnveloping_left_projective _root_.OAI.ArExplicit.twistedEnveloping_right_finite _root_.OAI.ArExplicit.twistedEnveloping_right_projective _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)

instance explicitBimodule_finite_left : Module.Finite (A k q) (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_left q H₁ H₂).1

instance explicitBimodule_projective_left : Module.Projective (A k q) (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_left q H₁ H₂).2

instance explicitBimodule_finite_right : Module.Finite (A k q)ᵐᵒᵖ (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_right q H₁ H₂).1

instance explicitBimodule_projective_right : Module.Projective (A k q)ᵐᵒᵖ (explicitBimodule q H₁ H₂) :=
  (explicitBimodule_right q H₁ H₂).2

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_ATwistedCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.T.explicitBimodule_finite_left _root_.OAI.ArExplicit.T.explicitBimodule_finite_right _root_.OAI.ArExplicit.T.explicitBimodule_projective_left _root_.OAI.ArExplicit.T.explicitBimodule_projective_right _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
theorem nativeEvaluationIso_eq :
    BalancedTensor.nativeEvaluationIso (A.simpleFiniteModule q) (evaluatedTwistEquiv q H) =
      evaluatedTwistIso q H := rfl

end ArExplicit.T

end

end OAI
end


