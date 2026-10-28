-- Prove2me | Definitions.Def_OAIQ031A129
-- name    : OAIQ031A129
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:06:03.109809+00:00
-- url     : https://prove2.me/theorems/63ae032d-132f-409d-964b-28557f3fd450
-- title:
--   Definitions bundle OAIQ031A129 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 7 definitions, 1 inductive type or structure and 11 theorems. The definitions and types are `OAI.ArExplicit.A.fullHomZeroScalarEquiv`, `OAI.ArExplicit.A.fullNonnegativeExtEquiv`, `OAI.ArExplicit.A.simpleComplete`, `OAI.ArExplicit.A.simpleExtZeroEquiv`, `OAI.ArExplicit.FiniteLeftModule.fullPositiveModuleExtEquiv`, `OAI.ArExplicit.FullPositive.NonnegativeChart`, `OAI.ArExplicit.Resolution.tPMul`, `OAI.ArExplicit.TwoCone.negativeTopCokernelEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Evaluation_ConcreteBetaHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteBetaHom.lean), [`AuslanderReiten_Ext_TExplicitGenerator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitGenerator.lean), [`AuslanderReiten_Ext_TExplicitPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExplicitPolynomial.lean), [`AuslanderReiten_Ext_TExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtPolynomial.lean), [`AuslanderReiten_HomComplex_FiniteFullHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomExt.lean), [`AuslanderReiten_HomComplex_FiniteFullHomZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomZero.lean), [`AuslanderReiten_HomComplex_TensorFullHomPositive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/TensorFullHomPositive.lean), [`AuslanderReiten_HomComplex_TensorFullHomZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/TensorFullHomZero.lean), [`AuslanderReiten_Homology_FullPositiveModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/FullPositiveModel.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A107`, `OAIQ031A118`, `OAIQ031A119` and `OAIQ031A124` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A139`, `OAIQ031A140` and `OAIQ031A142`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A107
import Definitions.Def_OAIQ031A118
import Definitions.Def_OAIQ031A119
import Definitions.Def_OAIQ031A124

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

def negativeTopCokernelEquiv (n : ℕ) :
    ConeCokernel.Right (-(D.d (n + 4))) ≃ₗ[R] BaseCokernel D (n + 4) :=
  Submodule.quotEquivOfEq _ _ (by simp)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBetaHom
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.A
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
theorem betaHom_ne_zero (hq : 1+q ≠ 0) : betaHom q ≠ 0 := by
  intro hz
  have hh := congrArg
    (FiniteLeftModule.resolutionHomotopyEquiv (AFrobeniusTrace k q)
      (simpleFiniteModule q) (betaFiniteModule q)) hz
  erw [betaHom, FiniteLeftModule.resolutionHomotopyEquiv_map, map_zero] at hh
  exact beta_stable_ne_zero q hq hh

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

theorem tSelfExt_coefficient (n : ℕ) (x : TSelfExt q (3 * n)) :
    ∃! a : k, a • tTauPower q hq hq1 h n = x := by
  let e := tExtCoefficientEquiv q hq hq1 h n
  refine ⟨e.symm x, ?_, ?_⟩
  · change e.symm x • e 1 = x
    rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  · intro a ha
    apply e.injective
    rw [e.apply_symm_apply]
    have he : e a = a • e 1 := by simpa using e.map_smul a (1 : k)
    exact he.trans ha

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitGenerator
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

theorem tExplicitP_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) : tExplicitP q ≠ 0 :=
  CocycleData.simpleExtClass_ne_zero q hq hq1

variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

@[simp] theorem tTauPower_one : tTauPower q hq hq1 h 1 = tTau q hq hq1 h := by
  change (tTau q hq hq1 h).comp (tTauPower q hq hq1 h 0) (by omega) = tTau q hq hq1 h
  rw [tTauPower_zero]
  exact Abelian.Ext.comp_mk₀_id _

theorem tExplicitP_generator : ∃ a : k, a ≠ 0 ∧ tExplicitP q = a • tTau q hq hq1 h := by
  obtain ⟨a, ha, _⟩ := tSelfExt_coefficient q hq hq1 h 1 (tExplicitP q)
  have hpa : tExplicitP q = a • tTau q hq hq1 h := by
    simpa only [tTauPower_one] using ha.symm
  refine ⟨a, ?_, hpa⟩
  intro ha0
  apply tExplicitP_ne_zero q hq hq1
  simpa only [ha0, zero_smul] using hpa

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExplicitPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
local notation "S" => ModuleCat.of T (Simple q)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

def tPMul (n : ℕ) : TSelfExt q n →ₗ[k] TSelfExt q (n + 3) :=
  Abelian.Ext.bilinearCompOfLinear k S S S 3 n (n + 3) (by omega) (tExplicitP q)

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomZero
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

theorem fullHomZeroEquiv_ofHom (f : M.completeCochain τ ⟶ N.completeCochain τ) :
    fullHomZeroEquiv τ M N (CohomologyClass.mk (Cocycle.ofHom f)) =
      StableHom.classOf R _ _ ((N.completeCochainCokernelEquiv τ).toLinearMap.comp
        ((cochainCokernelMap f).comp (M.completeCochainCokernelEquiv τ).symm.toLinearMap)) := by
  change StableHom.targetEquiv (k := k) (N.fullCokernelEquiv τ)
    (StableHom.sourceEquiv (k := k) (M.fullCokernelEquiv τ).symm
      (fullHomSourceStableLinearEquiv _ _ 0
        (M.completeCochain_totallyAcyclic τ).to_chain
        (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
        (CohomologyClass.mk (Cocycle.ofHom f)))) = _
  rw [fullHomSourceStableLinearEquiv_mk, sourceCocycleMap_ofHom (k := k),
    StableHom.sourceEquiv_classOf, StableHom.targetEquiv_classOf]
  congr 1
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f)
    ((M.fullCokernelEquiv τ).symm x)
  change (cochainCokernelLinearEquiv _) (cokernelMap (extendMap f negIndexEmbedding) 0
    ((M.fullCokernelEquiv τ).symm x)) = cochainCokernelMap f
      ((cochainCokernelLinearEquiv _) ((M.fullCokernelEquiv τ).symm x)) at h
  change (N.completeCochainCokernelEquiv τ)
    ((cochainCokernelLinearEquiv _) (cokernelMap (extendMap f negIndexEmbedding) 0
      ((M.fullCokernelEquiv τ).symm x))) = _
  rw [h]
  simp only [fullCokernelEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

@[simp]
theorem fullHomZeroEquiv_lift (f : M.carrier →ₗ[R] N.carrier) :
    fullHomZeroEquiv τ M N (CohomologyClass.mk (Cocycle.ofHom (resolutionMap τ f))) =
      StableHom.classOf R _ _ f := by
  rw [fullHomZeroEquiv_ofHom, resolutionMap_cokernel]
  congr 1
  ext x
  simp [resolutionCokernelMap]

@[simp]
theorem fullHomZeroEquiv_identity :
    fullHomZeroEquiv τ M M (CohomologyClass.mk (Cocycle.ofHom (𝟙 (M.completeCochain τ)))) =
      StableHom.identity := by
  rw [fullHomZeroEquiv_ofHom]
  change StableHom.classOf R _ _ _ = StableHom.classOf R _ _ LinearMap.id
  congr 1
  ext x
  change (M.completeCochainCokernelEquiv τ)
    (cochainCokernelMap (𝟙 _) ((M.completeCochainCokernelEquiv τ).symm x)) = x
  have hid : cochainCokernelMap (𝟙 (M.completeCochain τ)) = LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := (LinearMap.range ((M.completeCochain τ).d (-1) 0).hom).mkQ_surjective z
    rfl
  rw [hid]
  exact LinearEquiv.apply_symm_apply _ _

end FiniteLeftModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
open CompleteComparison
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def fullPositiveModuleExtEquiv (n : ℕ) :
    CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1:ℕ):ℤ) ≃ₗ[k]
      Ext M.carrier M.carrier (n+1) :=
  (fullPositiveExtEquiv (k := k) _ _ (M.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex n).trans
      (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso (n+1))

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_TensorFullHomZero
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def simpleComplete := (simpleFiniteModule q).completeCochain (AFrobeniusTrace k q)

def fullHomZeroScalarEquiv (hq1 : 1+q ≠ 0) :
    CohomologyClass (simpleComplete q) (simpleComplete q) 0 ≃ₗ[k] k :=
  (FiniteLeftModule.fullHomZeroEquiv (AFrobeniusTrace k q)
    (simpleFiniteModule q) (simpleFiniteModule q)).trans (stableEndEquiv q hq1)

@[simp]
theorem fullHomZeroScalarEquiv_identity (hq1 : 1+q ≠ 0) :
    fullHomZeroScalarEquiv q hq1 (CohomologyClass.mk (Cocycle.ofHom (𝟙 (simpleComplete q)))) = 1 := by
  change stableEndEquiv q hq1 (FiniteLeftModule.fullHomZeroEquiv (AFrobeniusTrace k q)
    (simpleFiniteModule q) (simpleFiniteModule q) _) = 1
  erw [FiniteLeftModule.fullHomZeroEquiv_identity, stableEndEquiv_identity]

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_TensorFullHomPositive
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
open CompleteComparison
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]

def simpleExtZeroEquiv (hq1 : 1+q ≠ 0) : k ≃ₗ[k] Ext (Simple q) (Simple q) 0 :=
  (simpleEndEquiv q hq1).symm.trans (nativeExtZeroEquiv (Simple q) (Simple q))

omit [CharP k 2] [HasDerivedCategory (ModuleCat.{u} (A k q))] in
@[simp]
theorem simpleExtZeroEquiv_one (hq1 : 1+q ≠ 0) :
    simpleExtZeroEquiv q hq1 1 = Ext.mk₀ (𝟙 (Simple q)) := by
  unfold simpleExtZeroEquiv
  rw [LinearEquiv.trans_apply, nativeExtZeroEquiv_apply]
  congr 1
  apply ModuleCat.hom_ext
  change (1:k) • (LinearMap.id : Simple q →ₗ[A k q] Simple q) = LinearMap.id
  exact one_smul k _

def fullNonnegativeExtEquiv (hq1 : 1+q ≠ 0) : (n : ℕ) →
    CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ) ≃ₗ[k] Ext (Simple q) (Simple q) n
  | 0 => (fullHomZeroScalarEquiv q hq1).trans (simpleExtZeroEquiv q hq1)
  | n+1 => FiniteLeftModule.fullPositiveModuleExtEquiv (AFrobeniusTrace k q) (simpleFiniteModule q) n

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
@[simp]
theorem fullNonnegativeExtEquiv_identity (hq1 : 1+q ≠ 0) :
    fullNonnegativeExtEquiv q hq1 0 (fullHomIdentity (simpleComplete q)) = Ext.mk₀ (𝟙 (Simple q)) := by
  change simpleExtZeroEquiv q hq1 (fullHomZeroScalarEquiv q hq1
    (CohomologyClass.mk (Cocycle.ofHom (𝟙 _)))) = _
  rw [fullHomZeroScalarEquiv_identity, simpleExtZeroEquiv_one]

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_FullPositiveModel
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullPositive
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : ModuleCat.{u} R)
open CompleteComparison TateKoszul
local notation "H" => CohomologyClass K K

structure NonnegativeChart where
  equiv : ∀ n : ℕ, H (n:ℤ) ≃ₗ[k] Ext X X n
  product : ∀ (n m : ℕ) (x : H (n:ℤ)) (y : H (m:ℤ)),
    equiv (n+m) (degreeEquiv (k := k) H (show (n:ℤ)+(m:ℤ)=((n+m:ℕ):ℤ) by omega)
      (fullHomProduct x y)) = (equiv n x).comp (equiv m y) rfl

end ArExplicit.FullPositive

end

end OAI
end


