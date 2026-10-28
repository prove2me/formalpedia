-- Prove2me | Definitions.Def_OAIQ031A126
-- name    : OAIQ031A126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:01:30.060342+00:00
-- url     : https://prove2.me/theorems/76c7f822-7ece-4398-81c8-dfd2161be434
-- title:
--   Definitions bundle OAIQ031A126 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 4 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.ArExplicit.T.barPairCoordinates`, `OAI.ArExplicit.TwistedBimodule.tensorRestrictionEquiv`, `OAI.ArExplicit.twistedEnvelopingRestrictionEquiv`, `OAI.ArExplicit.twistedEnvelopingRestrictionIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTwistAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistAction.lean), [`AuslanderReiten_Bar_ModuleBarTwistExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistExtAction.lean), [`AuslanderReiten_Cones_BimoduleTwoConeSides`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/BimoduleTwoConeSides.lean), [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Cones_TwoConeRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeRestriction.lean), [`AuslanderReiten_Coordinates_TensorTopComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopComparison.lean), [`AuslanderReiten_Evaluation_TensorEndpointEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorEndpointEvaluation.lean), [`AuslanderReiten_Tensor_TwistedEnvelopingFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedEnvelopingFunctor.lean), [`AuslanderReiten_Tensor_TwistedEnvelopingProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedEnvelopingProjective.lean), [`AuslanderReiten_Tensor_TwistedTensorFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorFunctor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A105`, `OAIQ031A106`, `OAIQ031A114`, `OAIQ031A115` and `OAIQ031A116` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A137`, `OAIQ031A154` and `OAIQ031A160`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A106
import Definitions.Def_OAIQ031A114
import Definitions.Def_OAIQ031A115
import Definitions.Def_OAIQ031A116

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (p : AbsoluteBar.Cochain3 k R) (c : k)
variable (hp : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hp

include he

theorem transportHom_suffixComparison (n : ℕ)
    (f : moduleObject k R M (n+1) →ₗ[R] M) :
    transportHom k R M h e he (n+4) (f.comp (suffixComparisonMap k R M p n)) =
      c • (transportHom k R M h e he (n+1) f).comp (suffixComparisonMap k R M p n) := by
  ext x
  change e.symm (f (suffixComparison k R M p (n+1) (transport k R M h e (n+4) x))) =
    c • e.symm (f (transport k R M h e (n+1) (suffixComparison k R M p (n+1) x)))
  erw [transport_suffixComparison k R M h e p c hp (n+1)]
  exact (congrArg e.symm ((f.restrictScalars k).map_smul c
    (transport k R M h e (n+1) (suffixComparison k R M p (n+1) x)))).trans
      (e.symm.map_smul c _)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

variable (c : k)
variable (hpc : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hpc

omit [HasDerivedCategory (ModuleCat R)] in
theorem transportedCochain_cubic (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M) :
    transportedCochain k R M h e he (n+3) (cubicMap k R M p n ≫ f) =
      c • (cubicMap k R M p n ≫ transportedCochain k R M h e he n f) := by
  apply ModuleCat.hom_ext
  exact transportHom_suffixComparison k R M h e he p c hpc n f.hom

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeProjective
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

theorem C₁_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (D.term n))
    [Module.Projective R (BaseCokernel D 0)] : Module.Projective R (C₁ D) :=
  cokernel_projective D hex (baseCokernel_projective D hex hp) 1

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

theorem C₁_side_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective S ((D.restrict j).term n))
    [Module.Projective S (BaseCokernel (D.restrict j) 0)] :
    Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R (C₁ D))) := by
  let := C₁_projective (D.restrict j) (restricted_exact j D hex) hp
  exact Module.Projective.of_equiv (cokernelRestrictionEquiv j D 1).symm

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoConeSides
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "A₀" => R ⊗[k] R
local notation "Ae" => ExternalTensor.EnvelopingProduct k R R
local notation "D" => bimoduleTwoConeData q

theorem firstTail_right_projective :
    Module.Projective A₀ᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let : Module.Projective A₀ᵐᵒᵖ
      (TwoCone.BaseCokernel ((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)) 0) :=
    Module.Projective.of_equiv (baseRightEquiv q).symm
  exact TwoCone.C₁_side_projective (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) D
    (bimodule_exact q) (baseTerm_right_projective q)

theorem firstTail_left_finite :
    Module.Finite A₀ ((ModuleCat.restrictScalars (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let := firstTail_finite q
  let := tensorLeftRegular_finite k A₀ A₀ᵐᵒᵖ
  exact restrict_finite (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) (ModuleCat.of Ae (firstTail q))

theorem firstTail_right_finite :
    Module.Finite A₀ᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).obj
      (ModuleCat.of Ae (firstTail q))) := by
  let := firstTail_finite q
  let := tensorRightRegular_finite k A₀ A₀ᵐᵒᵖ
  exact restrict_finite (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) (ModuleCat.of Ae (firstTail q))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R

theorem tensorTopComparison_chain (n : ℕ) :
    ((ExternalTensor.complex k Te Te P₀ P₀).d (n+2) (n+1)).hom.comp
      (tensorTopComparison q H (n+1)) =
    (tensorTopComparison q H n).comp ((productTwistedTotal q H).d (n+1) n).hom := by
  unfold tensorTopComparison
  rw [ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H), barB_chain]

theorem tensorTopComparison_zero :
    ((ExternalTensor.complex k Te Te P₀ P₀).d 1 0).hom.comp (tensorTopComparison q H 0) =
      tensorEndpoint q H := by
  unfold tensorTopComparison tensorEndpoint
  rw [ExternalTensor.bottomMap_d_target, barB_bottom]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorEndpointEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def barPairCoordinates := TensorProduct.congr
  (AbsoluteBar.scalarCoordinates k R 1) (AbsoluteBar.scalarCoordinates k R 1)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TwistedBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (σ : R ≃ₐ[k] R)

def tensorRestrictionEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (TwistedBimodule k R σ) M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M :=
  (tensorUntwist σ).trans (leftModuleCoordinates σ M)

@[simp] theorem tensorRestrictionEquiv_tmul (M : ModuleCat.{u} R)
    (a : TwistedBimodule k R σ) (m : M) :
    tensorRestrictionEquiv σ M (BalancedTensor.tmul a m) = σ.symm a.value • m := rfl

end ArExplicit.TwistedBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedEnvelopingFunctor
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.TriangularInduction.eRegular_projective _root_.OAI.ArExplicit.TriangularModule.instAddCommGroup _root_.OAI.ArExplicit.TriangularModule.instIsScalarTowerTriangular _root_.OAI.ArExplicit.TriangularModule.instModule _root_.OAI.ArExplicit.TriangularModule.instModuleTriangular _root_.OAI.ArExplicit.TriangularModule.instSMulTriangular _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def twistedEnvelopingRestrictionEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) M ≃ₗ[R]
      (ModuleCat.restrictScalars σ.symm.toRingHom).obj M :=
  (BalancedTensor.congrLeft (twistedEvaluationCoordinates σ) (LinearEquiv.refl k M)
    (twistedEvaluationCoordinates_right σ) (fun _ _ => rfl)
    (twistedEvaluationCoordinates_left σ)).trans (TwistedBimodule.tensorRestrictionEquiv σ M)

@[simp] theorem twistedEnvelopingRestrictionEquiv_tmul (M : ModuleCat.{u} R)
    (a : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (m : M) :
    twistedEnvelopingRestrictionEquiv σ M (BalancedTensor.tmul a m) =
      σ.symm a.value.value • m := rfl

def twistedEnvelopingRestrictionIso :
    BalancedTensor.functor (k := k) (R := R) (S := R)
      (F := EnvelopingBimodule k R (twistedFiniteModule σ).carrier) ≅
      ModuleCat.restrictScalars σ.symm.toRingHom :=
  NatIso.ofComponents (fun M => (twistedEnvelopingRestrictionEquiv σ M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.leftHom_ext
    intro a m
    change σ.symm a.value.value • f.hom m = f.hom (σ.symm a.value.value • m)
    exact (f.hom.map_smul _ _).symm)

instance twistedEnvelopingFunctor_equivalence :
    (BalancedTensor.functor (k := k) (R := R) (S := R)
      (F := EnvelopingBimodule k R (twistedFiniteModule σ).carrier)).IsEquivalence := by
  let := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv σ.symm.toRingEquiv
  exact Functor.isEquivalence_of_iso (twistedEnvelopingRestrictionIso σ).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedEnvelopingProjective
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)

instance twistedEnveloping_left_finite :
    Module.Finite R (EnvelopingBimodule k R (twistedFiniteModule σ).carrier) := by
  let := (twistedFiniteModule_left σ).1
  infer_instance

end ArExplicit

end

end OAI
end


