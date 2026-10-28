-- Prove2me | Definitions.Def_OAIQ031A055
-- name    : OAIQ031A055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:07:41.074608+00:00
-- url     : https://prove2.me/theorems/f6d480f3-0eb2-4a42-9eb4-280d9de5d8fb
-- title:
--   Definitions bundle OAIQ031A055 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 13 definitions, 3 instances and 16 theorems. The definitions and types are `OAI.ArExplicit.BimoduleFiber.bimodule`, `OAI.ArExplicit.BimoduleFiber.finiteModule`, `OAI.ArExplicit.BimoduleFiber.target`, `OAI.ArExplicit.EnvelopingBimodule.scalarCongr`, `OAI.ArExplicit.ExternalTensor.complexMap`, `OAI.ArExplicit.FiniteLeftModule.canonicalCosyzygies`, `OAI.ArExplicit.FiniteLeftModule.canonicalCosyzygy`, `OAI.ArExplicit.FiniteLeftModule.canonicalEmbedding`, `OAI.ArExplicit.FiniteLeftModule.fiber`, `OAI.ArExplicit.FiniteLeftModule.fiberMap`, `OAI.ArExplicit.FiniteLeftModule.fiberSource`, `OAI.ArExplicit.FiniteLeftModule.fiberSourceSideEquiv`, `OAI.ArExplicit.twistedFiniteModule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Ext_ExternalComplexIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalComplexIso.lean), [`AuslanderReiten_Fibers_BimoduleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/BimoduleFiber.lean), [`AuslanderReiten_Fibers_FiniteFiberSides`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteFiberSides.lean), [`AuslanderReiten_Fibers_FiniteModuleFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteModuleFiber.lean), [`AuslanderReiten_Modules_TwistedBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedBimodule.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Stable_CanonicalCosyzygy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/CanonicalCosyzygy.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedEquiv.lean), [`AuslanderReiten_Tensor_EnvelopingBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBimodule.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A026`, `OAIQ031A029`, `OAIQ031A035`, `OAIQ031A036` and `OAIQ031A037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A068`, `OAIQ031A071`, `OAIQ031A072` and `OAIQ031A074`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A029
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A036
import Definitions.Def_OAIQ031A037

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalComplexIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P P' P'' : ChainComplex (ModuleCat.{u} A) ℕ}
  {Q Q' Q'' : ChainComplex (ModuleCat.{u} B) ℕ}

abbrev complexMap (f : P ⟶ P') (g : Q ⟶ Q') :=
  mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)

@[reassoc] theorem inclusion_complexMap (f : P ⟶ P') (g : Q ⟶ Q')
    (i j n : ℕ) (h : i+j=n) :
    inclusion k A B P Q i j n h ≫ (complexMap k A B f g).f n =
      mapHom k A B (f.f i) (g.f j) ≫ inclusion k A B P' Q' i j n h := by
  change ιMapBifunctor P Q (bifunctor k A B) (ComplexShape.down ℕ) i j n h ≫
    (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ)).f n = _
  erw [ι_mapBifunctorMap]
  change mapHom k A B (f.f i) (𝟙 (Q.X j)) ≫
    mapHom k A B (𝟙 (P'.X i)) (g.f j) ≫ _ = _
  erw [← Category.assoc, ← mapHom_comp, Category.comp_id, Category.id_comp]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_CanonicalCosyzygy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

def canonicalEmbedding (M : FiniteLeftModule k R) : M.carrier ⟶ M.canonicalEnvelope :=
  ModuleCat.ofHom CoinducedModule.embedding

def canonicalCosyzygy (M : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := cokernelObject M.canonicalEmbedding
  scalar := inferInstanceAs (Module k (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))
  tower := inferInstanceAs (IsScalarTower k R
    (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))
  finite := inferInstanceAs (Module.Finite k
    (CoinducedModule k R M.carrier ⧸ LinearMap.range (CoinducedModule.embedding (k := k) (R := R) (M := M.carrier))))

def canonicalCosyzygies (M : FiniteLeftModule k R) : ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (canonicalCosyzygies M n).canonicalCosyzygy

variable {S : Type u} [Ring S] (j : S →+* R)
variable [Module.Injective S S]
variable [Module.Finite S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]

omit [Module.Injective S S] in
theorem canonicalEnvelope_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj M.canonicalEnvelope) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.canonicalEnvelope) := by
  let : Module.Finite R M.canonicalEnvelope := CoinducedModule.finite (M := M.carrier) τ
  let : Module.Projective R M.canonicalEnvelope := CoinducedModule.projective (M := M.carrier) τ
  exact ⟨restrict_finite j M.canonicalEnvelope, restrict_projective j M.canonicalEnvelope⟩

theorem canonicalCosyzygy_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
    [Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier)]
    [Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)] :
    Module.Finite S ((ModuleCat.restrictScalars j).obj M.canonicalCosyzygy.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.canonicalCosyzygy.carrier) := by
  obtain ⟨hfin, hproj⟩ := canonicalEnvelope_side j τ M
  let := hfin
  let := hproj
  let := finiteProjective_injective (R := S) (M := (ModuleCat.restrictScalars j).obj M.carrier)
  constructor
  · exact Module.Finite.equiv (restrictCokernelEquiv j M.canonicalEmbedding).symm
  · exact cokernel_restrict_projective j M.canonicalEmbedding CoinducedModule.embedding_injective

theorem canonicalCosyzygies_side (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
    [Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier)]
    [Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)] (n : ℕ) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (M.canonicalCosyzygies n).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (M.canonicalCosyzygies n).carrier) := by
  induction n with
  | zero =>
    change Module.Finite S ((ModuleCat.restrictScalars j).obj M.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj M.carrier)
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    exact canonicalCosyzygy_side j τ (M.canonicalCosyzygies n)

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteModuleFiber
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory
open scoped TensorProduct

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

theorem canonicalFreeCoverMap_surjective (Y : FiniteLeftModule k R) :
    Function.Surjective Y.canonicalFreeCoverMap.hom := by
  intro y
  exact ⟨1 ⊗ₜ[k] y, one_smul R y⟩

theorem canonicalFreeCover_finite (Y : FiniteLeftModule k R) :
    Module.Finite R Y.canonicalFreeCover.carrier :=
  Module.Finite.of_basis ((Module.finBasis k Y.carrier).baseChange R)

theorem canonicalFreeCover_projective (Y : FiniteLeftModule k R) :
    Module.Projective R Y.canonicalFreeCover.carrier := by
  change Module.Projective R (R ⊗[k] Y.carrier)
  infer_instance

variable (U₁ U₂ Y : FiniteLeftModule k R)

def fiberSource : FiniteLeftModule k R where
  carrier := ModuleCat.of R (U₁.carrier × U₂.carrier × Y.canonicalFreeCover.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

def fiberMap (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    (fiberSource U₁ U₂ Y).carrier ⟶ Y.carrier :=
  ModuleCat.ofHom (g₁.hom.coprod (g₂.hom.coprod Y.canonicalFreeCoverMap.hom))

theorem fiberMap_surjective (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    Function.Surjective (fiberMap U₁ U₂ Y g₁ g₂).hom := by
  intro y
  obtain ⟨z, hz⟩ := canonicalFreeCoverMap_surjective Y y
  refine ⟨(0, 0, z), ?_⟩
  change g₁.hom 0 + (g₂.hom 0 + Y.canonicalFreeCoverMap.hom z) = y
  simpa using hz

def fiber (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) : FiniteLeftModule k R where
  carrier := kernelObject (fiberMap U₁ U₂ Y g₁ g₂)
  scalar := inferInstanceAs (Module k (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom))
  tower := inferInstanceAs (IsScalarTower k R (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom))
  finite := by
    change Module.Finite k (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom)
    exact Module.Finite.of_injective
      (((LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom).subtype).restrictScalars k) Subtype.val_injective

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteFiberSides
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R S : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [Ring S] (j : S →+* R)
variable (U₁ U₂ Y : FiniteLeftModule k R)

def fiberSourceSideEquiv :
    ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) ≃ₗ[S]
      (((ModuleCat.restrictScalars j).obj U₁.carrier) ×
        ((ModuleCat.restrictScalars j).obj U₂.carrier) ×
        ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]

theorem canonicalFreeCover_side :
    Module.Finite S ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj Y.canonicalFreeCover.carrier) := by
  let := canonicalFreeCover_finite Y
  let := canonicalFreeCover_projective Y
  exact ⟨restrict_finite j _, restrict_projective j _⟩

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₂.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₂.carrier)]

theorem fiberSource_side :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (fiberSource U₁ U₂ Y).carrier) := by
  obtain ⟨hfin, hproj⟩ := canonicalFreeCover_side j Y
  let := hfin
  let := hproj
  exact ⟨Module.Finite.equiv (fiberSourceSideEquiv j U₁ U₂ Y).symm,
    Module.Projective.of_equiv (fiberSourceSideEquiv j U₁ U₂ Y).symm⟩

theorem fiber_side [Module.Projective S ((ModuleCat.restrictScalars j).obj Y.carrier)]
    (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier) :
    Module.Finite S ((ModuleCat.restrictScalars j).obj (fiber U₁ U₂ Y g₁ g₂).carrier) ∧
      Module.Projective S ((ModuleCat.restrictScalars j).obj (fiber U₁ U₂ Y g₁ g₂).carrier) := by
  obtain ⟨hfin, hproj⟩ := fiberSource_side j U₁ U₂ Y
  let := hfin
  let := hproj
  exact ⟨kernel_restrict_finite j (fiberMap U₁ U₂ Y g₁ g₂)
      (fiberMap_surjective U₁ U₂ Y g₁ g₂),
    kernel_restrict_projective j (fiberMap U₁ U₂ Y g₁ g₂)
      (fiberMap_surjective U₁ U₂ Y g₁ g₂)⟩

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance instProjective : Module.Projective R (TwistedBimodule k R σ) :=
  Module.Projective.of_equiv (leftLinearEquiv σ).symm

instance instFinite : Module.Finite R (TwistedBimodule k R σ) :=
  Module.Finite.equiv (leftLinearEquiv σ).symm

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

instance instProjectiveOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion [Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Projective R (EnvelopingBimodule k R M) :=
  Module.Projective.of_equiv (leftEquiv M).symm

end EnvelopingBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_BimoduleFiber
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def twistedFiniteModule (σ : R ≃ₐ[k] R) : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ) where
  carrier := bimoduleEnvelopingObject k R (TwistedBimodule k R σ)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstanceAs (Module.Finite k (TwistedBimodule k R σ))

theorem twistedFiniteModule_left (σ : R ≃ₐ[k] R) :
    Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) ∧
    Module.Projective R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj
      (twistedFiniteModule σ).carrier) :=
  ⟨Module.Finite.equiv (bimoduleEnvelopingLeftEquiv k R (TwistedBimodule k R σ)).symm,
    Module.Projective.of_equiv (bimoduleEnvelopingLeftEquiv k R (TwistedBimodule k R σ)).symm⟩

namespace BimoduleFiber

variable (C₁ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

abbrev target := C₁.canonicalCosyzygies 4

variable (σ₁ σ₂ : R ≃ₐ[k] R)
variable (g₁ : (twistedFiniteModule σ₁).carrier ⟶ (target C₁).carrier)
variable (g₂ : (twistedFiniteModule σ₂).carrier ⟶ (target C₁).carrier)

abbrev finiteModule : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ) :=
  FiniteLeftModule.fiber (twistedFiniteModule σ₁) (twistedFiniteModule σ₂) (target C₁) g₁ g₂

abbrev bimodule := EnvelopingBimodule k R (finiteModule C₁ σ₁ σ₂ g₁ g₂).carrier

end BimoduleFiber
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem row_column (n : ℕ) : (row k (n + 1)).comp (column k n) = 0 := by
  apply LinearMap.ext
  intro w
  change mulX k (n + 1) (mulY k n w) + mulY k (n + 1) (-(mulX k n w)) = 0
  rw [map_neg, ← LinearMap.comp_apply, mul_commute]
  simp

theorem column_injective (n : ℕ) : Function.Injective (column k n) := by
  intro f g h
  apply mulY_injective k n
  exact congrArg Prod.fst h

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def scalarCongr : EnvelopingBimodule k R M ≃ₗ[k] EnvelopingBimodule k R N where
  toFun x := ⟨e x.value⟩
  invFun y := ⟨e.symm y.value⟩
  left_inv x := by ext; exact e.symm_apply_apply x.value
  right_inv y := by ext; exact e.apply_symm_apply y.value
  map_add' x y := by ext; exact e.map_add _ _
  map_smul' c x := by ext; exact (e.restrictScalars k).map_smul c x.value

@[simp] theorem scalarCongr_left (a : R) (x : EnvelopingBimodule k R M) :
    scalarCongr e (a • x) = a • scalarCongr e x := by
  ext
  exact e.map_smul (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x.value

@[simp] theorem scalarCongr_right (a : Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    scalarCongr e (a • x) = a • scalarCongr e x := by
  ext
  exact e.map_smul ((1 : R) ⊗ₜ[k] a) x.value

end ArExplicit.EnvelopingBimodule

end

end OAI
end


