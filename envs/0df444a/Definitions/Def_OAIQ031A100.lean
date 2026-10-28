-- Prove2me | Definitions.Def_OAIQ031A100
-- name    : OAIQ031A100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:37:49.29986+00:00
-- url     : https://prove2.me/theorems/f05ed790-9b85-490e-a0c6-2720006cad08
-- title:
--   Definitions bundle OAIQ031A100 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.barFreeCoordinate`, `OAI.ArExplicit.ExternalTensor.barTotalFreeCoordinate`, `OAI.ArExplicit.ModuleBar.cyclicCover`, `OAI.ArExplicit.TwoCone.middleD`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarFreeCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarFreeCoordinate.lean), [`AuslanderReiten_Bar_ExternalBarTotalFree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarTotalFree.lean), [`AuslanderReiten_Bar_ModuleBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarFreeAugmentation.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Ext_ExternalEvaluationComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationComparison.lean), [`AuslanderReiten_Tensor_ExternalTensorAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorAugmentation.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A080` and `OAIQ031A085` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A107`, `OAIQ031A111`, `OAIQ031A112`, `OAIQ031A115` and `OAIQ031A116`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A085

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

def cyclicCover : R →ₗ[R] moduleObject k R M 0 where
  toFun a := a • e.symm 1
  map_add' a b := add_smul a b _
  map_smul' a b := by
    change (a * b) • e.symm 1 = a • (b • e.symm 1)
    exact mul_smul a b _

@[simp] theorem cyclicCover_apply (a : R) :
    cyclicCover k R M e a = a • e.symm 1 := rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreeCoordinate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def barFreeCoordinate :
    letI := moduleCatBaseModule (k := k) (R := A) (ModuleBar.moduleObject k A M 1)
    letI := moduleCatBaseModule (k := k) (R := B) (ModuleBar.moduleObject k B N 1)
    letI := moduleCatBaseTower (k := k) (R := A) (ModuleBar.moduleObject k A M 1)
    letI := moduleCatBaseTower (k := k) (R := B) (ModuleBar.moduleObject k B N 1)
    moduleObject k A B (ModuleBar.moduleObject k A M 1) (ModuleBar.moduleObject k B N 1) ⟶
      ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  mapHom k A B (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
    (ModuleBar.freeCoordinate k B N f).toModuleIso.hom ≫
    (canonicalTensorIso k A B A B).hom ≫ (regularEquiv k A B).toModuleIso.hom

theorem barFreeCoordinate_tmul
    (x : ModuleBar.moduleObject k A M 1) (y : ModuleBar.moduleObject k B N 1) :
    barFreeCoordinate k A B M N e f
      (canonicalTmul k A B (ModuleBar.moduleObject k A M 1)
        (ModuleBar.moduleObject k B N 1) x y) =
      ModuleBar.freeCoordinate k A M e x ⊗ₜ[k] ModuleBar.freeCoordinate k B N f y := by
  change regularEquiv k A B ((canonicalTensorIso k A B A B).hom
    (canonicalTmul k A B A B (ModuleBar.freeCoordinate k A M e x)
      (ModuleBar.freeCoordinate k B N f y))) = _
  rw [canonicalTensorIso_tmul]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

theorem singleTotalZeroEquiv_insert (x : moduleObject k A B M N) :
    singleTotalZeroEquiv k A B M N
      (cubicInsert k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
        ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 ⟨(0,0),rfl⟩ x) = x := by
  let e := termDirectSumEquiv k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
    ((ChainComplex.single₀ (ModuleCat B)).obj N) 0
  change (e (e.symm (DFinsupp.single ⟨(0,0),rfl⟩ x))) ⟨(0,0),rfl⟩ = x
  rw [LinearEquiv.apply_symm_apply]
  exact DFinsupp.single_eq_same

theorem singleTotalIso_inclusion :
    inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl ≫
        (singleTotalIso k A B M N).hom.f 0 = 𝟙 (moduleObject k A B M N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change singleTotalZeroEquiv k A B M N
    ((inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl).hom x) = x
  rw [inclusion_eq_cubicInsert]
  exact singleTotalZeroEquiv_insert k A B M N x

variable {M N} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

theorem inclusion_augmentation :
    inclusion k A B P.complex Q.complex 0 0 0 rfl ≫ (augmentation k A B P Q).f 0 =
      mapHom k A B (P.π.f 0) (Q.π.f 0) := by
  unfold augmentation
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  rw [show inclusion k A B P.complex Q.complex 0 0 0 rfl ≫
      (mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ)).f 0 =
    ((bifunctor k A B).map (P.π.f 0)).app (Q.complex.X 0) ≫
      ((bifunctor k A B).obj (((ChainComplex.single₀ (ModuleCat A)).obj M).X 0)).map (Q.π.f 0) ≫
        inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
          ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl from
      ι_mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) 0 0 0 rfl]
  erw [Category.assoc, Category.assoc, singleTotalIso_inclusion, Category.comp_id]
  change mapHom k A B (P.π.f 0) (𝟙 _) ≫ mapHom k A B (𝟙 _) (Q.π.f 0) = _
  rw [← mapHom_comp, Category.comp_id, Category.id_comp]

theorem augmentation_insert (x : moduleObject k A B (P.complex.X 0) (Q.complex.X 0)) :
    (augmentation k A B P Q).f 0 (cubicInsert k A B P.complex Q.complex 0 ⟨(0,0),rfl⟩ x) =
      mapHom k A B (P.π.f 0) (Q.π.f 0) x := by
  have h := congrArg (fun f => f.hom x) (inclusion_augmentation k A B P Q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusion_eq_cubicInsert] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarTotalFree
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N] [CharP k 2]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def barTotalFreeCoordinate :
    (complex k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex).X 0 ⟶
        ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  ModuleCat.ofHom (bottomProjection k A B (ModuleBar.nativeResolution k A M).complex
    (ModuleBar.nativeResolution k B N).complex 0) ≫ barFreeCoordinate k A B M N e f

theorem inclusion_barTotalFreeCoordinate :
    inclusion k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex 0 0 0 rfl ≫
        barTotalFreeCoordinate k A B M N e f = barFreeCoordinate k A B M N e f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change barFreeCoordinate k A B M N e f
    (bottomProjection k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex 0
      ((inclusion k A B (ModuleBar.nativeResolution k A M).complex
        (ModuleBar.nativeResolution k B N).complex 0 0 0 rfl).hom x)) = _
  rw [inclusion_eq_cubicInsert, bottomProjection_bottom]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def middleD (n : ℕ) : middleTerm D (n + 1) →ₗ[R] middleTerm D n :=
  (D.d (n + 2)).prodMap (D.d (n + 2))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationComparison
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
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (P' : ChainComplex (ModuleCat.{u} A) ℕ) (Q' : ChainComplex (ModuleCat.{u} B) ℕ)
variable (a : factorEvaluation k X P ⟶ P') (b : factorEvaluation k Y Q ⟶ Q')

@[reassoc] theorem inclusion_evaluatedComparison (i j n : ℕ) (h : i+j=n) :
    (productEvaluation k A B X Y).map
      (ExternalTensor.inclusion k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) P Q i j n h) ≫
      ((totalEvaluationTermIso k A B X Y P Q n).hom ≫
        (ExternalTensor.complexMap k A B a b).f n) =
    (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom ≫
      ExternalTensor.mapHom k A B (a.f i) (b.f j) ≫
        ExternalTensor.inclusion k A B P' Q' i j n h :=
  compose_after (inclusion_totalEvaluationTermIso k A B X Y P Q i j n h)
    (ExternalTensor.inclusion_complexMap k A B a b i j n h)

end ArExplicit.ExternalBalanced

end

end OAI
end


