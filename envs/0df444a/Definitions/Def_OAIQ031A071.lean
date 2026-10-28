-- Prove2me | Definitions.Def_OAIQ031A071
-- name    : OAIQ031A071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:16:35.039133+00:00
-- url     : https://prove2.me/theorems/cb6fd0e5-0f3d-4c5f-8d6a-4599409d6900
-- title:
--   Definitions bundle OAIQ031A071 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 4 definitions, 1 instance and 10 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.tensorCongr`, `OAI.ArExplicit.EnvelopingBimodule.tensorProdMap`, `OAI.ArExplicit.ExternalBalanced.bimoduleCoordinates`, `OAI.ArExplicit.ExternalTensor.envelopingScalarEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cocycles_CocycleTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleTwist.lean), [`AuslanderReiten_Fibers_BimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/BimoduleFiber.lean), [`AuslanderReiten_Modules_InductionBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionBimodule.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedEquiv.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProduct.lean), [`AuslanderReiten_Tensor_ExternalBalancedCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedCoordinates.lean), [`AuslanderReiten_Tensor_ExternalEnvelopingScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalEnvelopingScalar.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A047`, `OAIQ031A049`, `OAIQ031A050`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A055` and `OAIQ031A056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A085`, `OAIQ031A086` and `OAIQ031A089`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A050
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A053
import Definitions.Def_OAIQ031A055
import Definitions.Def_OAIQ031A056

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem p_twist (H : kˣ) (a b c : T k q) :
    p q (TrivialExtension.twist H a) (TrivialExtension.twist H b) (TrivialExtension.twist H c) =
      (H : k) • TrivialExtension.twist H (p q a b c) := by
  rw [p_apply, p_apply, map_list_sum, List.smul_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hw := (cochain_term_properties t ht).2.2.2.2.2
  have hpow : (H : k) ^ t.first.weight * (H : k) ^ t.second.weight * (H : k) ^ t.third.weight =
      (H : k) * (H : k) ^ t.output.weight := by
    rw [← pow_add, ← pow_add, hw, pow_succ']
  simp only [evalTriple, coefficient_twist, map_smul, twist_vector, smul_smul]
  congr 1
  calc
    _ = ((H : k) ^ t.first.weight * (H : k) ^ t.second.weight * (H : k) ^ t.third.weight) *
      (q ^ t.degree * T.coefficient q t.first a * T.coefficient q t.second b * T.coefficient q t.third c) := by ring
    _ = _ := by rw [hpow]; ring

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_BimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

theorem twistedFiniteModule_right (σ : R ≃ₐ[k] R) :
    Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) ∧
    Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) :=
  ⟨Module.Finite.equiv (bimoduleEnvelopingRightEquiv k R (TwistedBimodule k R σ)).symm,
    Module.Projective.of_equiv (bimoduleEnvelopingRightEquiv k R (TwistedBimodule k R σ)).symm⟩

namespace BimoduleFiber

variable (C₁ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

variable (σ₁ σ₂ : R ≃ₐ[k] R)
variable (g₁ : (twistedFiniteModule σ₁).carrier ⟶ (target C₁).carrier)
variable (g₂ : (twistedFiniteModule σ₂).carrier ⟶ (target C₁).carrier)

theorem target_left (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective R R]
    [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) ∧
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) := by
  let := tensorLeftRegular_finite k R Rᵐᵒᵖ
  let := tensorLeftRegular_projective k R Rᵐᵒᵖ
  exact C₁.canonicalCosyzygies_side (tensorLeftInclusion k R Rᵐᵒᵖ) τ 4

theorem target_right (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ]
    [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) ∧
    Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj (target C₁).carrier) := by
  let := tensorRightRegular_finite k R Rᵐᵒᵖ
  let := tensorRightRegular_projective k R Rᵐᵒᵖ
  exact C₁.canonicalCosyzygies_side (tensorRightInclusion k R Rᵐᵒᵖ) τ 4

theorem left (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective R R]
    [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite R (bimodule C₁ σ₁ σ₂ g₁ g₂) ∧
      Module.Projective R (bimodule C₁ σ₁ σ₂ g₁ g₂) := by
  let := tensorLeftRegular_finite k R Rᵐᵒᵖ
  let := tensorLeftRegular_projective k R Rᵐᵒᵖ
  obtain ⟨hYfin, hYproj⟩ := target_left C₁ τ
  let := hYfin
  let := hYproj
  obtain ⟨hU₁fin, hU₁proj⟩ := twistedFiniteModule_left σ₁
  let := hU₁fin
  let := hU₁proj
  obtain ⟨hU₂fin, hU₂proj⟩ := twistedFiniteModule_left σ₂
  let := hU₂fin
  let := hU₂proj
  obtain ⟨hfin, hproj⟩ := FiniteLeftModule.fiber_side (tensorLeftInclusion k R Rᵐᵒᵖ)
    (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂
  let := hfin
  let := hproj
  exact ⟨inferInstance, inferInstance⟩

theorem right (τ : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ)) [Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ]
    [Module.Finite Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)]
    [Module.Projective Rᵐᵒᵖ ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj C₁.carrier)] :
    Module.Finite Rᵐᵒᵖ (bimodule C₁ σ₁ σ₂ g₁ g₂) ∧
      Module.Projective Rᵐᵒᵖ (bimodule C₁ σ₁ σ₂ g₁ g₂) := by
  let := tensorRightRegular_finite k R Rᵐᵒᵖ
  let := tensorRightRegular_projective k R Rᵐᵒᵖ
  obtain ⟨hYfin, hYproj⟩ := target_right C₁ τ
  let := hYfin
  let := hYproj
  obtain ⟨hU₁fin, hU₁proj⟩ := twistedFiniteModule_right σ₁
  let := hU₁fin
  let := hU₁proj
  obtain ⟨hU₂fin, hU₂proj⟩ := twistedFiniteModule_right σ₂
  let := hU₂fin
  let := hU₂proj
  obtain ⟨hfin, hproj⟩ := FiniteLeftModule.fiber_side (tensorRightInclusion k R Rᵐᵒᵖ)
    (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂
  let := hfin
  let := hproj
  exact ⟨inferInstance, inferInstance⟩

end BimoduleFiber
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

namespace InductionBimodule
variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (ι : R →ₐ[k] S)

instance instFinite : Module.Finite S (InductionBimodule ι) := Module.Finite.equiv (leftEquiv ι).symm

end InductionBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (e : M ≃ₗ[R ⊗[k] Rᵐᵒᵖ] N)

variable (X : ModuleCat.{u} R) [Module k X]

def tensorCongr : BalancedTensor k R (EnvelopingBimodule k R M) X ≃ₗ[R]
    BalancedTensor k R (EnvelopingBimodule k R N) X :=
  BalancedTensor.congrLeft (scalarCongr e) (LinearEquiv.refl k X)
    (scalarCongr_right e) (fun _ _ => rfl) (scalarCongr_left e)

@[simp] theorem tensorCongr_tmul (m : EnvelopingBimodule k R M) (x : X) :
    tensorCongr e X (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (⟨e m.value⟩ : EnvelopingBimodule k R N) x := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
  [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
  [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (X : ModuleCat.{u} R) [Module k X]
local notation "ProdMN" => ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)
local notation "EM" => BalancedTensor k R (EnvelopingBimodule k R M) X
local notation "EN" => BalancedTensor k R (EnvelopingBimodule k R N) X
local notation "EP" => BalancedTensor k R (EnvelopingBimodule k R ProdMN) X

def tensorProdMap : EP →ₗ[R] EM × EN :=
  (tensorMap (k := k) X (ModuleCat.ofHom (X := ProdMN) (Y := M) (LinearMap.fst (R ⊗[k] Rᵐᵒᵖ) M N))).prod
    (tensorMap (k := k) X (ModuleCat.ofHom (X := ProdMN) (Y := N) (LinearMap.snd (R ⊗[k] Rᵐᵒᵖ) M N)))

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnvelopingScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def envelopingScalarEquiv (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    envelopingObject k A B M ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (envelopingEquiv k A B).symm (algebraMap k (EnvelopingProduct k A B) a) • (show M from x) =
      a • (show M from x)
    rw [AlgEquiv.commutes, algebraMap_smul]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))

def bimoduleCoordinates : exteriorBimodule k A B M N ≃ₗ[k]
    (EnvelopingBimodule k A M) ⊗[k] (EnvelopingBimodule k B N) :=
  (EnvelopingBimodule.scalarEquiv _).trans
    ((ExternalTensor.envelopingScalarEquiv k A B _).trans
      ((ExternalTensor.moduleScalarCoordinates k Ae Be M N).trans
        (TensorProduct.congr (EnvelopingBimodule.scalarEquiv M).symm
          (EnvelopingBimodule.scalarEquiv N).symm)))

@[simp] theorem bimoduleCoordinates_symm_tmul (m : EnvelopingBimodule k A M)
    (n : EnvelopingBimodule k B N) :
    ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n)).value =
      m.value ⊗ₜ[k] n.value := rfl

theorem bimoduleCoordinates_right (a : A) (b : B)
    (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    MulOpposite.op (a ⊗ₜ[k] b) • (bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n) =
      (bimoduleCoordinates k A B M N).symm
        ((MulOpposite.op a • m) ⊗ₜ[k] (MulOpposite.op b • n)) := by
  apply EnvelopingBimodule.ext
  change ExternalTensor.representation k Ae Be M N ((ExternalTensor.envelopingEquiv k A B).symm
    (((1 : A) ⊗ₜ[k] (1 : B)) ⊗ₜ[k] MulOpposite.op (a ⊗ₜ[k] b)))
      (m.value ⊗ₜ[k] n.value) = _
  rw [ExternalTensor.envelopingEquiv_symm_tmul]
  rfl

theorem bimoduleCoordinates_left (a : A) (b : B)
    (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    (a ⊗ₜ[k] b) • (bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n) =
      (bimoduleCoordinates k A B M N).symm ((a • m) ⊗ₜ[k] (b • n)) := by
  apply EnvelopingBimodule.ext
  change ExternalTensor.representation k Ae Be M N ((ExternalTensor.envelopingEquiv k A B).symm
    ((a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op ((1 : A) ⊗ₜ[k] (1 : B))))
      (m.value ⊗ₜ[k] n.value) = _
  rw [ExternalTensor.envelopingEquiv_symm_tmul]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
end


