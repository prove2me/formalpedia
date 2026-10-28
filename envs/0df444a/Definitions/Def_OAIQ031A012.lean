-- Prove2me | Definitions.Def_OAIQ031A012
-- name    : OAIQ031A012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:00:00.88002+00:00
-- url     : https://prove2.me/theorems/8d6981a3-16e8-473c-b220-413d432a3dd9
-- title:
--   Definitions bundle OAIQ031A012 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 5 definitions and 16 theorems. The definitions and types are `OAI.ArExplicit.ResolutionProducts.closedCochain`, `OAI.ArExplicit.ResolutionProducts.conjugateTo`, `OAI.ArExplicit.ResolutionProducts.extOfCocycle`, `OAI.ArExplicit.TIndex.vertex`, `OAI.ArExplicit.rightTensorIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_Radical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/Radical.lean), [`AuslanderReiten_Algebras_TensorRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorRadical.lean), [`AuslanderReiten_Cocycles_CocycleCorners`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCorners.lean), [`AuslanderReiten_Ext_CubicExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/CubicExtAction.lean), [`AuslanderReiten_Ext_CubicExtCommute`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/CubicExtCommute.lean), [`AuslanderReiten_Ext_ExtCentralGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtCentralGeneration.lean), [`AuslanderReiten_Ext_ExtGenerationTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtGenerationTransfer.lean), [`AuslanderReiten_Ext_ExtTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtTensorAction.lean), [`AuslanderReiten_Ext_NatCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/NatCubicExt.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Resolutions_ResolutionExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtAction.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A035`, `OAIQ031A038` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem jacobson_eq_bot_of_equiv (e : R ≃+* S) (hS : Ring.jacobson S = ⊥) :
    Ring.jacobson R = ⊥ := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  apply le_antisymm _ bot_le
  intro x hx
  have h := Ring.le_comap_jacobson e.toRingHom hx
  rw [hS] at h
  exact e.injective (by simpa using h)

theorem field_jacobson_eq_bot (k : Type*) [Field k] : Ring.jacobson k = ⊥ := by
  let : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
  exact le_antisymm (Ring.jacobson_le_of_isMaximal ⊥) bot_le

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightTensorIdeal (I : Ideal S) : Ideal (R ⊗[k] S) :=
  I.map (Algebra.TensorProduct.includeRight : S →ₐ[k] R ⊗[k] S)

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
namespace TIndex

def vertex (b : Bool) : TIndex := (false, if b then .f else .e)

end TIndex

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_NatCubicExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (n+4) (n+3) ≫ f n)
include hf

theorem natCubic_augmented_cycle : P.complex.d 4 3 ≫ (f 0 ≫ P.π.f 0) = 0 := by
  rw [← Category.assoc, ← hf 0, Category.assoc, P.complex_d_comp_π_f_zero,
    CategoryTheory.Limits.comp_zero]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

def conjugateTo {X X' Y Y' : DerivedCategory C} (e : X ≅ X') (t : Y ≅ Y')
    {n : ℤ} (f : ShiftedHom X Y n) : ShiftedHom X' Y' n :=
  e.inv ≫ f ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) n).map t.hom

theorem conjugateTo_comp {X X' Y Y' Z Z' : DerivedCategory C}
    (e : X ≅ X') (t : Y ≅ Y') (w : Z ≅ Z')
    {n m r : ℤ} (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m) (h : m+n=r) :
    conjugateTo e w (f.comp g h) = (conjugateTo e t f).comp (conjugateTo t w g) h := by
  simp only [conjugateTo, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((CategoryTheory.shiftFunctor (DerivedCategory C) n).map t.hom),
    ← Functor.map_comp, t.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun z => e.inv ≫ f ≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) n).map g ≫ z)
      ((CategoryTheory.shiftFunctorAdd' (DerivedCategory C) m n r h).inv.naturality w.hom).symm

variable [HasExt.{v} C]

def extOfCocycle {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    Ext X Y n := P.extEquivCohomologyClass.symm (CohomologyClass.mk y)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_CubicExtAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

def closedCochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat R) 0).obj Y) (n : ℤ) :=
  Cocycle.toSingleMk ((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f) (by omega)
    (-((n+1 : ℕ) : ℤ)) (by omega) (by
      rw [P.cochainComplex_d _ _ (n+1) n rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hf, CategoryTheory.Limits.comp_zero])

omit [HasDerivedCategory (ModuleCat.{u} R)] in
@[simp] theorem extOf_closedCochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    extOfCocycle P (closedCochain P f hf) = P.extMk f (n+1) rfl hf := rfl

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
include hp

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cubicPrecomp_closed {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    P.complex.d (n+4) (n+3) ≫ (p n ≫ f)=0 := by
  rw [← Category.assoc, ← hp n, Category.assoc, hf, CategoryTheory.Limits.comp_zero]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_CubicExtCommute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f g : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ f n)
variable (hg : ∀ n, g (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ g n)

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem extMk_eq_of_map_eq {n : ℕ} (a b : P.complex.X n ⟶ X)
    (ha : P.complex.d (n+1) n ≫ a = 0) (hb : P.complex.d (n+1) n ≫ b = 0)
    (hab : a = b) : P.extMk a (n+1) rfl ha = P.extMk b (n+1) rfl hb := by
  subst b
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtCentralGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {X : ModuleCat.{u} R}

theorem scalar_end_hom (M : ModuleCat.{u} R) (f : M ⟶ M) (c : k)
    (hf : ∀ x : M, f.hom x = (algebraMap k R c) • x) : f = c • (𝟙 M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hf x

theorem extZero_scalar_of_hom
    (h : ∀ f : X ⟶ X, ∃ c : k, f = c • 𝟙 X) (x : Ext X X 0) :
    ∃ c : k, x = c • Ext.mk₀ (𝟙 X) := by
  obtain ⟨c,hc⟩ := h (Ext.homEquiv₀ x)
  refine ⟨c, ?_⟩
  exact (Ext.mk₀_homEquiv₀_apply x).symm.trans
    ((congrArg Ext.mk₀ hc).trans (Ext.mk₀_smul (R := k) c (𝟙 X)))

theorem commute_step (a b : Ext X X 3) (n : ℕ) (x : Ext X X (3*n))
    (hab : a.comp b rfl = b.comp a rfl)
    (hax : a.comp x (by omega : 3+3*n=3*(n+1)) =
      x.comp a (by omega : 3*n+3=3*(n+1))) :
    a.comp (b.comp x (by omega : 3+3*n=3*(n+1))) (by omega : 3+3*(n+1)=3*(n+2)) =
      (b.comp x (by omega : 3+3*n=3*(n+1))).comp a
        (by omega : 3*(n+1)+3=3*(n+2)) := by
  rw [← Ext.comp_assoc a b x rfl (by omega : 3+3*n=3*(n+1)) (by omega)]
  rw [hab]
  rw [Ext.comp_assoc b a x rfl (by omega : 3+3*n=3*(n+1)) (by omega)]
  rw [hax]
  rw [← Ext.comp_assoc b x a (by omega : 3+3*n=3*(n+1))
    (by omega : 3*n+3=3*(n+1)) (by omega)]

theorem cubicCentral_of_generation (a b : Ext X X 3)
    (hab : a.comp b rfl = b.comp a rfl)
    (hzero : ∀ x : Ext X X 0,
      a.comp x (by omega : 3+0=3) = x.comp a (by omega : 0+3=3) ∧
      b.comp x (by omega : 3+0=3) = x.comp b (by omega : 0+3=3))
    (hgen : ∀ (n : ℕ) (x : Ext X X (3*(n+1))), ∃ u v : Ext X X (3*n),
      x = a.comp u (by omega) + b.comp v (by omega)) :
    ∀ (n : ℕ) (x : Ext X X (3*n)),
      a.comp x (by omega : 3+3*n=3*(n+1)) = x.comp a (by omega) ∧
      b.comp x (by omega : 3+3*n=3*(n+1)) = x.comp b (by omega) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro x
    obtain ⟨u,v,rfl⟩ := hgen n x
    constructor
    · rw [Ext.comp_add, Ext.add_comp]
      exact congrArg₂ (· + ·) (commute_step a a n u rfl (ih u).1)
        (commute_step a b n v hab (ih v).1)
    · rw [Ext.comp_add, Ext.add_comp]
      exact congrArg₂ (· + ·) (commute_step b a n u hab.symm (ih u).2)
        (commute_step b b n v rfl (ih v).2)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtGenerationTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {R : Type u} [Ring R] {X : ModuleCat.{u} R}
variable {D₀ D₁ : Type u} [AddCommGroup D₀] [AddCommGroup D₁]

theorem generationOfAddEquiv {n : ℕ} (a b : Ext X X 3)
    (e₀ : Ext X X n ≃+ D₀) (e₁ : Ext X X (n+3) ≃+ D₁)
    (f g : D₀ → D₁)
    (ha : ∀ x, e₁ (a.comp x (by omega)) = f (e₀ x))
    (hb : ∀ x, e₁ (b.comp x (by omega)) = g (e₀ x))
    (hgen : ∀ z : D₁, ∃ u v, z = f u + g v)
    (x : Ext X X (n+3)) :
    ∃ u v : Ext X X n, x = a.comp u (by omega) + b.comp v (by omega) := by
  obtain ⟨u,v,huv⟩ := hgen (e₁ x)
  refine ⟨e₀.symm u,e₀.symm v,e₁.injective ?_⟩
  rw [map_add,ha,hb,AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  exact huv

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtTensorAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

theorem extMk_of_eq {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (L : ProjectiveResolution M) {n : ℕ} (f g : L.complex.X n ⟶ N)
    (hf : L.complex.d (n+1) n ≫ f=0) (hg : L.complex.d (n+1) n ≫ g=0) (hfg : f=g) :
    L.extMk f (n+1) rfl hf = L.extMk g (n+1) rfl hg := by
  subst g
  rfl

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)

omit [HasDerivedCategory (ModuleCat.{u} A)] [∀ n, Module.Finite A (P.complex.X n)] in
include hp in
theorem firstFactor_closed (i : ℕ) (f : P.complex.X i →ₗ[A] U)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) :
    (f.comp (p i).hom).comp (P.complex.d (i+4) (i+3)).hom=0 :=
  congrArg ModuleCat.Hom.hom (ResolutionProducts.cubicPrecomp_closed P p hp
    (ModuleCat.ofHom (X := P.complex.X i) (Y := U) f) (ModuleCat.hom_ext hf))

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [HasDerivedCategory (ModuleCat.{u} B)] [∀ n, Module.Finite B (Q.complex.X n)] in
include hr in
theorem secondFactor_closed (j : ℕ) (g : Q.complex.X j →ₗ[B] V)
    (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (g.comp (r j).hom).comp (Q.complex.d (j+4) (j+3)).hom=0 :=
  congrArg ModuleCat.Hom.hom (ResolutionProducts.cubicPrecomp_closed Q r hr
    (ModuleCat.ofHom (X := Q.complex.X j) (Y := V) g) (ModuleCat.hom_ext hg))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

omit [CommRing k] in
@[simp]
theorem snoc_castSucc_succ {n : ℕ} (f : Fin (n + 1) → k) (a : k) (i : Fin n) :
    (Fin.snoc f a : Fin (n + 2) → k) i.castSucc.succ = f i.succ := by
  rw [← Fin.castSucc_succ, Fin.snoc_castSucc]

end ArExplicit.BinaryKoszul

end OAI
end


