-- Prove2me | Definitions.Def_OAIQ031A007
-- name    : OAIQ031A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:05.992019+00:00
-- url     : https://prove2.me/theorems/5d7a91db-41bd-492f-9da2-73f141b9c76f
-- title:
--   Definitions bundle OAIQ031A007 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 17 definitions, 1 instance and 17 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullHomIdentity`, `OAI.ArExplicit.ExternalTensor.freeCoordinates`, `OAI.ArExplicit.ExternalTensor.homCochain`, `OAI.ArExplicit.Resolution.NoPositivePowerOne`, `OAI.ArExplicit.ResolutionHomology.cyclesToExt`, `OAI.ArExplicit.ResolutionHomology.differential`, `OAI.ArExplicit.StableHomology.Cokernel`, `OAI.ArExplicit.StableHomology.cycleToMap`, `OAI.ArExplicit.StableHomology.precomp`, `OAI.ArExplicit.StableTargetHomology.cycleToMap`, `OAI.ArExplicit.StableTargetHomology.postcomp`, `OAI.ArExplicit.extSourceIso`, `OAI.ArExplicit.extTargetIso`, `OAI.ArExplicit.nativeExtMkZero`, `OAI.ArExplicit.nativeExtZeroEquiv`, `OAI.ArExplicit.nonnegativeTail`, `OAI.ArExplicit.selfExtIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Bar_ModuleBar`, `AuslanderReiten_Complete_CompleteResolutionTail`, `AuslanderReiten_Duality_LinearHomologyDuality`, `AuslanderReiten_Ext_ExtIsoCongr`, `AuslanderReiten_Ext_NativeExtZero`, `AuslanderReiten_HomComplex_FullHomDegreeProducts`, `AuslanderReiten_Homology_VectorTensorKunneth`, `AuslanderReiten_Resolutions_CProjectiveResolution`, `AuslanderReiten_Resolutions_NatResolutionCochain`, `AuslanderReiten_Resolutions_ResolutionHomology`, `AuslanderReiten_Stable_StableExtEquiv`, `AuslanderReiten_Stable_StableHomology`, `AuslanderReiten_Stable_StableTargetHomology`, `AuslanderReiten_Tensor_ExternalTensorHomComplex`, `AuslanderReiten_Tensor_ExternalTensorProjective`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034`, `OAIQ031A036`, `OAIQ031A038`, `OAIQ031A040` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

variable [CharP k 2]

theorem double_zero_p0 {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R : Type u} [Ring R]

def nonnegativeTail (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => P.X (n : ℤ))
    (fun n => P.d ((n + 1 : ℕ) : ℤ) (n : ℤ))
    (fun _n => P.d_comp_d _ _ _)

@[simp]
theorem nonnegativeTail_d (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (nonnegativeTail P).d (n + 1) n = P.d ((n + 1 : ℕ) : ℤ) (n : ℤ) := by
  simp [nonnegativeTail]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_LinearHomologyDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

theorem dual_comp (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    f.dualMap.comp g.dualMap = 0 := by
  ext φ x
  change φ (g (f x)) = 0
  rw [show g (f x) = 0 from DFunLike.congr_fun h x, map_zero]

end ArExplicit.LinearHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtIsoCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {X X' Y Y' : C}

def extSourceIso (e : X ≅ X') (Y : C) (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

def extTargetIso (X : C) (e : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X Y' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' c x := by simp

def selfExtIso (e : X ≅ Y) (n : ℕ) : Ext X X n ≃ₗ[k] Ext Y Y n :=
  (extSourceIso (k := k) e X n).trans (extTargetIso (k := k) Y e n)

@[simp]
theorem selfExtIso_apply (e : X ≅ Y) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) e n x =
      ((Ext.mk₀ e.inv).comp x (zero_add n)).comp (Ext.mk₀ e.hom) (add_zero n) := rfl

@[simp]
theorem selfExtIso_identity (e : X ≅ Y) :
    selfExtIso (k := k) e 0 (Ext.mk₀ (𝟙 X)) = Ext.mk₀ (𝟙 Y) := by
  simp

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_NativeExtZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} R) [Module k N] [IsScalarTower k R N]

def nativeExtMkZero : (M →ₗ[R] N) →ₗ[k] Ext M N 0 where
  toFun f := Ext.mk₀ (ModuleCat.ofHom f)
  map_add' f g := by rw [ModuleCat.ofHom_add, Ext.mk₀_add]
  map_smul' c f := by
    rw [← Ext.mk₀_smul]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change c • f x = (algebraMap k R c) • f x
    exact (IsScalarTower.algebraMap_smul R c (f x)).symm

def nativeExtZeroEquiv : (M →ₗ[R] N) ≃ₗ[k] Ext M N 0 :=
  LinearEquiv.ofBijective (nativeExtMkZero M N)
    ((Ext.mk₀_bijective M N).comp
      ⟨fun _f _g h => ModuleCat.hom_ext_iff.mp h, fun f => ⟨f.hom,rfl⟩⟩)

@[simp]
theorem nativeExtZeroEquiv_apply (f : M →ₗ[R] N) :
    nativeExtZeroEquiv (k := k) M N f = Ext.mk₀ (ModuleCat.ofHom f) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomDegreeProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m l : ℤ}

def fullHomIdentity (K : CochainComplex C ℤ) : CohomologyClass K K 0 :=
  CohomologyClass.mk (Cocycle.ofHom (𝟙 K))

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorTensorKunneth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.VectorComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

instance hasMapBifunctor (P Q : ChainComplex (ModuleCat.{u} k) ℕ) :
    HasMapBifunctor P Q F (ComplexShape.down ℕ) := fun _ => inferInstance

end ArExplicit.VectorComplex

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CProjectiveResolution
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

def NoPositivePowerOne : Prop := ∀ m : ℕ, 0 < m → 1 + q ^ m ≠ 0

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_NatResolutionCochain
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

include k in
theorem intUnit_smul_charTwo [CharP k 2] {M : Type u} [AddCommGroup M] [Module k M]
    (a : ℤˣ) (x : M) : a • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · exact one_smul _ x
  · change (-1 : ℤ) • x = x
    rw [neg_one_zsmul]
    have hx : x+x=0 := by
      rw [← two_smul k x, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_iff_add_eq_zero.mpr hx).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionHomology
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionHomology
universe u v w
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
variable {X Y : C} (P : ProjectiveResolution X)

def differential (n : ℕ) : (P.complex.X n ⟶ Y) →ₗ[k] (P.complex.X (n + 1) ⟶ Y) where
  toFun f := P.complex.d (n + 1) n ≫ f
  map_add' f g := by simp only [Preadditive.comp_add]
  map_smul' a f := by simp only [Linear.comp_smul, RingHom.id_apply]

@[simp] theorem differential_apply (n : ℕ) (f : P.complex.X n ⟶ Y) :
    differential (k := k) P n f = P.complex.d (n + 1) n ≫ f := rfl

theorem differential_comp (n : ℕ) :
    (differential (k := k) (Y := Y) P (n + 1)).comp (differential P n) = 0 := by
  ext f
  change P.complex.d (n + 2) (n + 1) ≫ (P.complex.d (n + 1) n ≫ f) = 0
  rw [← Category.assoc, P.complex.d_comp_d, Limits.zero_comp]

variable [HasExt.{w} C]

theorem extMk_smul (n : ℕ) (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) (a : k) :
    P.extMk (a • f) (n + 1) rfl (by simp [hf]) = a • P.extMk f (n + 1) rfl hf := by
  rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
  congr 1
  simp

def cyclesToExt (n : ℕ) :
    LinearMap.ker (differential (k := k) (Y := Y) P (n + 1)) →ₗ[k] Ext X Y (n + 1) where
  toFun f := P.extMk f.val (n + 2) rfl f.property
  map_add' f g := (P.add_extMk f.val g.val _ rfl f.property g.property).symm
  map_smul' a f := extMk_smul P (n + 1) f.val f.property a

theorem cyclesToExt_surjective (n : ℕ) :
    Function.Surjective (cyclesToExt (k := k) (Y := Y) P n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := P.extMk_surjective a (n + 2) rfl
  exact ⟨⟨f, hf⟩, hfa⟩

end ArExplicit.ResolutionHomology

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtEquiv
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}
variable (N : ModuleCat.{u} R)

theorem closed_of_indices {i j : ℤ} (h : i = j+1)
    (f : P.X j →ₗ[R] N) (hf : f.comp (P.d i j).hom = 0) :
    f.comp (P.d (j+1) j).hom = 0 := by
  subst i
  exact hf

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHomology
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [AddCommGroup N] [Module R N]
variable [Module k N] [IsScalarTower k R N]

def precomp {L M : Type u} [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    (f : L →ₗ[R] M) : (M →ₗ[R] N) →ₗ[k] (L →ₗ[R] N) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem precomp_comp (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    (precomp (k := k) (N := N) e).comp (precomp d) = 0 := by
  ext f x
  change f (d (e x)) = 0
  rw [show d (e x) = 0 from DFunLike.congr_fun h x, map_zero]

abbrev Cokernel (e : P₁ →ₗ[R] P₀) := P₀ ⧸ LinearMap.range e

def cycleToMap (e : P₁ →ₗ[R] P₀)
    (z : LinearMap.ker (precomp (k := k) (N := N) e)) : Cokernel e →ₗ[R] N :=
  (LinearMap.range e).liftQ z.val (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun z.property x)

@[simp]
theorem cycleToMap_mkQ (e : P₁ →ₗ[R] P₀)
    (z : LinearMap.ker (precomp (k := k) (N := N) e)) (x : P₀) :
    cycleToMap e z ((LinearMap.range e).mkQ x) = z.val x := rfl

end ArExplicit.StableHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableTargetHomology
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableTargetHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [AddCommGroup N] [Module R N]

def postcomp {L M : Type u} [AddCommGroup L] [Module R L] [Module k L]
    [IsScalarTower k R L] [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] (f : L →ₗ[R] M) : (N →ₗ[R] L) →ₗ[k] (N →ₗ[R] M) where
  toFun g := f.comp g
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

theorem postcomp_comp (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0) :
    (postcomp (k := k) (N := N) d).comp (postcomp e) = 0 := by
  ext f x
  exact DFunLike.congr_fun h (f x)

def cycleToMap (d : P₀ →ₗ[R] Pminus)
    (z : LinearMap.ker (postcomp (k := k) (N := N) d)) : N →ₗ[R] LinearMap.ker d :=
  z.val.codRestrict _ (fun x => DFunLike.congr_fun z.property x)

end ArExplicit.StableTargetHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorProjective
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeCoordinates (n m : ℕ) :
    (Fin n → A) ⊗[k] (Fin m → B) ≃ₗ[k] (Fin n → Fin m → A ⊗[k] B) :=
  (TensorProduct.piLeft k (Fin m → B) (fun _ : Fin n => A)).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k A (fun _ : Fin m => B))

@[simp] theorem freeCoordinates_tmul (n m : ℕ) (a : Fin n → A) (b : Fin m → B)
    (i : Fin n) (j : Fin m) :
    freeCoordinates k A B n m (a ⊗ₜ[k] b) i j = (a i) ⊗ₜ[k] (b j) := by
  simp [freeCoordinates, TensorProduct.piLeft, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomComplex
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def homCochain (U : Type u) [AddCommGroup U] [Module A U] [Module k U]
    [IsScalarTower k A U] : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (P.X n →ₗ[A] U))
    (fun n => ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro x
      change f ((P.d (n+1) n).hom ((P.d (n+2) (n+1)).hom x)) = 0
      have hz := congrArg (fun g => g.hom x) (P.d_comp_d (n+2) (n+1) n)
      change (P.d (n+1) n).hom ((P.d (n+2) (n+1)).hom x) = 0 at hz
      rw [hz, map_zero])

@[simp] theorem homCochain_d (U : Type u) [AddCommGroup U] [Module A U] [Module k U]
    [IsScalarTower k A U] (n : ℕ) :
    (homCochain k A P U).d n (n+1) =
      ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom) :=
  by
    exact CochainComplex.of_d (V := ModuleCat.{u} k)
      (fun n => ModuleCat.of k (P.X n →ₗ[A] U))
      (fun n => ModuleCat.ofHom (LinearMap.lcomp k U (P.d (n+1) n).hom)) n

end ArExplicit.ExternalTensor

end

end OAI
end


