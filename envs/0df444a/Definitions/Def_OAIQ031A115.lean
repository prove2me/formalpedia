-- Prove2me | Definitions.Def_OAIQ031A115
-- name    : OAIQ031A115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:51:41.095437+00:00
-- url     : https://prove2.me/theorems/ef295ce1-92cc-448a-96b5-9cfb65bd293b
-- title:
--   Definitions bundle OAIQ031A115 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 10 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.T.baseLeftEquiv`, `OAI.ArExplicit.T.baseQuotientRestriction`, `OAI.ArExplicit.T.baseRightEquiv`, `OAI.ArExplicit.T.baseToTensorRegular`, `OAI.ArExplicit.T.bimoduleBaseCokernelEquiv`, `OAI.ArExplicit.T.productBaseCokernelEquiv`, `OAI.ArExplicit.T.productBaseRestricted`, `OAI.ArExplicit.T.productBaseTyped`, `OAI.ArExplicit.T.tensorBarResolution`, `OAI.ArExplicit.T.tensorTopComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTwistAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistAction.lean), [`AuslanderReiten_Bar_ModuleBarTwistIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistIdentity.lean), [`AuslanderReiten_Bar_TBarHomotopies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TBarHomotopies.lean), [`AuslanderReiten_Bar_TBarLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TBarLift.lean), [`AuslanderReiten_Cones_BimoduleTwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/BimoduleTwoCone.lean), [`AuslanderReiten_Cones_BimoduleTwoConeExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/BimoduleTwoConeExact.lean), [`AuslanderReiten_Cones_BimoduleTwoConeSides`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/BimoduleTwoConeSides.lean), [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_TensorTopComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopComparison.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A092`, `OAIQ031A093`, `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A098`, `OAIQ031A099`, `OAIQ031A100`, `OAIQ031A101` and `OAIQ031A102` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A125` and `OAIQ031A126`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A092
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A098
import Definitions.Def_OAIQ031A099
import Definitions.Def_OAIQ031A100
import Definitions.Def_OAIQ031A101
import Definitions.Def_OAIQ031A102

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

theorem transport_suffixComparison (n : ℕ) (x : object k R M (n+3)) :
    suffixComparison k R M p n (transport k R M h e (n+3) x) =
      c • transport k R M h e n (suffixComparison k R M p n x) := by
  induction n with
  | zero => exact transport_suffix3 k R M h e p c hp x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul a x =>
      change suffixComparison k R M p (n+1)
        (h a ⊗ₜ[k] transport k R M h e (n+3) x) = _
      rw [suffixComparison_succ_tmul, ih, suffixComparison_succ_tmul, transport_tmul,
        TensorProduct.tmul_smul]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistIdentity
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem transportedCochain_augmentation :
    transportedCochain k R M h e he 0 ((resolution k R M).π.f 0) =
      (resolution k R M).π.f 0 := by
  change transportedCochain k R M h e he 0 ((augmentation k R M).f 0) =
      (augmentation k R M).f 0
  rw [augmentation_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change e.symm (boundary k R M 0 (transport k R M h e 1 x)) = boundary k R M 0 x
  exact (congrArg e.symm (transport_boundary k R M h e he 0 x).symm).trans
    (e.symm_apply_apply (boundary k R M 0 x))

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

variable [CharP k 2]

theorem B_differential_zero (H : kˣ) :
    (AbsoluteBar.differential k R 1).comp (B q H 1) =
      (B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0) :=
  AbsoluteBar.casimirInsertionMap_boundary_zero k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) (twistedCasimir_augmentation q H)

end ArExplicit.T

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

theorem baseCokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (D.term n))
    [Module.Projective R (BaseCokernel D 0)] (n : ℕ) :
    Module.Projective R (BaseCokernel D n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    let := hp n
    let := projective_kernel_of_surjective (LinearMap.range (D.d n)).mkQ
      (Submodule.mkQ_surjective _)
    exact Module.Projective.of_equiv (baseSuccessorEquiv D hex n).symm

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoCone
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k : Type u} [Field k] (q : k) [CharP k 2]
local notation "R" => T k q

theorem bimodule_term_finite (n : ℕ) :
    Module.Finite (ExternalTensor.EnvelopingProduct k R R) ((bimoduleTwoConeData q).term n) := by
  let := product_term_finite q n
  exact Module.Finite.of_surjective
    (ExternalTensor.envelopingSemilinear k R R ((productTwoConeData q).term n)).toLinearMap
    (ExternalTensor.envelopingSemilinear k R R ((productTwoConeData q).term n)).surjective

theorem firstTail_finite : Module.Finite (ExternalTensor.EnvelopingProduct k R R) (firstTail q) :=
  TwoCone.cokernel_finite _ (bimodule_term_finite q) 1

theorem bimodule_term_projective (n : ℕ) :
    Module.Projective (ExternalTensor.EnvelopingProduct k R R) ((bimoduleTwoConeData q).term n) := by
  let := product_term_projective q n
  exact ExternalTensor.enveloping_projective k R R ((productTwoConeData q).term n)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarHomotopies
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "P₀" => AbsoluteBar.complex k R

theorem barB_bottom : barB q H 0 ≫ (P₀).d 1 0 = barDb q H := by
  rw [AbsoluteBar.complex_d]
  apply ModuleCat.hom_ext
  exact B_differential_zero q H

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoConeExact
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

def tensorBarResolution : ProjectiveResolution
    (ExternalTensor.moduleObject k Te Te (AbsoluteBar.moduleObject k R 0)
      (AbsoluteBar.moduleObject k R 0)) := by
  letI (n : ℕ) : Module.Finite Te ((AbsoluteBar.resolution k R).complex.X n) :=
    AbsoluteBar.finite k R n
  exact ExternalTensor.projectiveResolution k Te Te (AbsoluteBar.resolution k R)
    (AbsoluteBar.resolution k R)

theorem product_exact (n : ℕ) :
    Function.Exact ((productTwoConeData q).d (n+1)) ((productTwoConeData q).d n) := by
  let (degree : ℕ) : Module.Finite Te ((AbsoluteBar.resolution k R).complex.X degree) :=
    AbsoluteBar.finite k R degree
  exact ExternalTensor.differential_exact k Te Te (AbsoluteBar.resolution k R)
    (AbsoluteBar.resolution k R) n

theorem bimodule_exact (n : ℕ) :
    Function.Exact ((bimoduleTwoConeData q).d (n+1)) ((bimoduleTwoConeData q).d n) :=
  product_exact q n

def productBaseCokernelEquiv :=
  resolutionCokernelEquiv (tensorBarResolution q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoConeSides
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def productBaseTyped : TwoCone.BaseCokernel (productTwoConeData q) 0 ≃ₗ[
    AbsoluteBar.Enveloping k R ⊗[k] AbsoluteBar.Enveloping k R]
    ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k R) (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R 0) (AbsoluteBar.moduleObject k R 0) :=
  productBaseCokernelEquiv q

def baseQuotientRestriction : TwoCone.BaseCokernel D 0 ≃ₗ[Ae]
    (ExternalTensor.envelopingFunctor k R R).obj
      (ModuleCat.of (ExternalTensor.ProductEnveloping k R R)
        (TwoCone.BaseCokernel (productTwoConeData q) 0)) := by
  unfold bimoduleTwoConeData
  convert! (TwoCone.baseCokernelRestrictionEquiv (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    (productTwoConeData q) 0).symm using 1
  all_goals try with_reducible_and_instances rfl

def productBaseRestricted := Iso.toLinearEquiv
  ((ExternalTensor.envelopingFunctor k R R).mapIso (productBaseTyped q).toModuleIso)

def baseToTensorRegular := (baseQuotientRestriction q).trans (productBaseRestricted q)

def bimoduleBaseCokernelEquiv : TwoCone.BaseCokernel D 0 ≃ₗ[Ae] AbsoluteBar.moduleObject k A₀ 0 :=
  (baseToTensorRegular q).trans (barTensorZeroEquiv k R R)

def baseLeftEquiv :
    TwoCone.BaseCokernel ((D).restrict (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)) 0 ≃ₗ[A₀] A₀ :=
  TwoCone.baseCokernelTransport (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) D 0
    (N := ModuleCat.of A₀ A₀) (bimoduleBaseCokernelEquiv q) (barZeroLeftEquiv k A₀)

def baseRightEquiv :
    TwoCone.BaseCokernel ((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)) 0 ≃ₗ[A₀ᵐᵒᵖ] A₀ᵐᵒᵖ :=
  TwoCone.baseCokernelTransport (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) D 0
    (N := ModuleCat.of A₀ᵐᵒᵖ A₀ᵐᵒᵖ) (bimoduleBaseCokernelEquiv q) (barZeroRightEquiv k A₀)

theorem baseTerm_left_projective (n : ℕ) :
    Module.Projective A₀ (((D).restrict (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ)).term n) := by
  let := bimodule_term_finite q n
  let := bimodule_term_projective q n
  let := tensorLeftRegular_projective k A₀ A₀ᵐᵒᵖ
  exact restrict_projective (tensorLeftInclusion k A₀ A₀ᵐᵒᵖ) ((D).term n)

theorem baseTerm_right_projective (n : ℕ) :
    Module.Projective A₀ᵐᵒᵖ (((D).restrict (tensorRightInclusion k A₀ A₀ᵐᵒᵖ)).term n) := by
  let := bimodule_term_finite q n
  let := bimodule_term_projective q n
  let := tensorRightRegular_projective k A₀ A₀ᵐᵒᵖ
  exact restrict_projective (tensorRightInclusion k A₀ A₀ᵐᵒᵖ) ((D).term n)

end ArExplicit.T

end

end OAI
end

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

theorem attachingRow_comm (n : ℕ) :
    (D.d n).comp (attachingRow D (n + 1)) = (attachingRow D n).comp (middleD D (n + 1)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change D.d n (D.first (n + 1) x + D.second (n + 1) y) =
    D.first n (D.d (n + 3) x) + D.second n (D.d (n + 3) y)
  rw [map_add]
  exact congrArg₂ (· + ·) (DFunLike.congr_fun (D.first_comm n) x)
    (DFunLike.congr_fun (D.second_comm n) y)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def tensorTopComparison (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ n (n+1) (barB q H n) (barDb q H)

@[simp] theorem tensorHighB_eq (n : ℕ) :
    tensorHighB q H n = tensorTopComparison q H (n+3) := rfl

end ArExplicit.T

end

end OAI
end


