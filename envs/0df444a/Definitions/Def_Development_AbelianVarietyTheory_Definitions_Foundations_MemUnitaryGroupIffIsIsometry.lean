-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:07.953941+00:00
-- url     : https://prove2.me/theorems/c276eea8-848f-43c9-acd5-1a6213603cef
-- title:
--   Mem Unitary Group Iff Is Isometry
-- statement:
--   Definitions and structural lemmas for Mem Unitary Group Iff Is Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
namespace GlobalTheory
abbrev SesqForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R
structure HermForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] where

  toSesq : SesqForm R M
  star_apply' : ∀ x y, star (toSesq x y) = toSesq y x
namespace HermForm
section Ring
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
instance : FunLike (HermForm R M) M (M →ₗ⋆[R] R) where
  coe h := h.toSesq
  coe_injective f g H := by
    cases f; cases g; congr; exact DFunLike.coe_injective H
instance : LinearMapClass (HermForm R M) R M (M →ₗ⋆[R] R) where
  map_add h := h.toSesq.map_add
  map_smulₛₗ h := h.toSesq.map_smul
@[simp] theorem toSesq_apply (h : HermForm R M) (x : M) : h.toSesq x = h x := rfl
@[simp] theorem mk_apply (B : SesqForm R M) (hB) (x : M) : (⟨B, hB⟩ : HermForm R M) x = B x := rfl
@[ext] theorem ext {h h' : HermForm R M} (H : ∀ x y, h x y = h' x y) : h = h' :=
  DFunLike.ext _ _ fun x => LinearMap.ext (H x)
variable (h : HermForm R M)
@[simp] theorem star_apply (x y : M) : star (h x y) = h y x := h.star_apply' x y
@[simp] theorem conj_apply (x y : M) : starRingEnd R (h x y) = h y x := h.star_apply' x y
theorem add_left (x y z : M) : h (x + y) z = h x z + h y z := by simp
theorem zero_left (y : M) : h 0 y = 0 := by simp
theorem smul_left (a : R) (x y : M) : h (a • x) y = a * h x y := by simp
theorem apply_eq_zero_comm (x y : M) : h x y = 0 ↔ h y x = 0 := by
  rw [← h.star_apply x y, star_eq_zero]
def ofFun (f : M → M → R) (add_left : ∀ x y z, f (x + y) z = f x z + f y z)
    (smul_left : ∀ (a : R) x y, f (a • x) y = a * f x y)
    (star_symm : ∀ x y, star (f x y) = f y x) : HermForm R M where
  toSesq := LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) f add_left smul_left
    (fun x y z => by rw [← star_symm, add_left, star_add, star_symm, star_symm])
    (fun a x y => by rw [← star_symm, smul_left, star_mul', star_symm]; rfl)
  star_apply' := star_symm
@[simp] theorem ofFun_apply (f : M → M → R) (h₁ h₂ h₃) (x y : M) :
    ofFun f h₁ h₂ h₃ x y = f x y := rfl
def comap (f : N →ₗ[R] M) : HermForm R N :=
  ofFun (fun x y => h (f x) (f y)) (by simp) (by simp) (by simp)
@[simp] theorem comap_apply (f : N →ₗ[R] M) (x y : N) : h.comap f x y = h (f x) (f y) := rfl
@[simp] theorem comap_id : h.comap LinearMap.id = h := rfl
def restrict (W : Submodule R M) : HermForm R W := h.comap W.subtype
@[simp] theorem restrict_apply (W : Submodule R M) (x y : W) :
    h.restrict W x y = h x y := rfl
def toDual : M →ₗ⋆[R] Module.Dual R M := h.toSesq.flip
@[simp] theorem toDual_apply (y x : M) : h.toDual y x = h x y := rfl
def Nondegenerate : Prop := h.toSesq.Nondegenerate
def Unimodular : Prop := Function.Bijective h.toDual
theorem nondegenerate_iff_left : h.Nondegenerate ↔ ∀ x, (∀ y, h x y = 0) → x = 0 :=
  ⟨fun H => H.1, fun H => ⟨H, fun y hy => H y fun x => (h.apply_eq_zero_comm x y).1 (hy x)⟩⟩
theorem nondegenerate_iff_right : h.Nondegenerate ↔ ∀ y, (∀ x, h x y = 0) → y = 0 :=
  ⟨fun H => H.2, fun H => ⟨fun x hx => H x fun y => (h.apply_eq_zero_comm x y).1 (hx y), H⟩⟩
theorem nondegenerate_iff_injective : h.Nondegenerate ↔ Function.Injective h.toDual := by
  rw [nondegenerate_iff_right, injective_iff_map_eq_zero]
  simp [LinearMap.ext_iff]
theorem unimodular_iff :
    h.Unimodular ↔ h.Nondegenerate ∧ ∀ φ : Module.Dual R M, ∃ y, ∀ x, h x y = φ x := by
  rw [nondegenerate_iff_injective]
  refine and_congr_right fun _ => forall_congr' fun φ => exists_congr fun y => ?_
  simp [LinearMap.ext_iff]
variable {h}
theorem Nondegenerate.eq_zero_left (H : h.Nondegenerate) {x : M} (hx : ∀ y, h x y = 0) : x = 0 :=
  H.1 x hx
theorem Unimodular.nondegenerate (H : h.Unimodular) : h.Nondegenerate :=
  (h.unimodular_iff.1 H).1
noncomputable def Unimodular.toDualEquiv (H : h.Unimodular) : M ≃ₗ⋆[R] Module.Dual R M :=
  LinearEquiv.ofBijective h.toDual H
@[simp] theorem Unimodular.toDualEquiv_apply (H : h.Unimodular) (y x : M) :
    H.toDualEquiv y x = h x y := rfl
@[simp] theorem Unimodular.apply_toDualEquiv_symm (H : h.Unimodular) (φ : Module.Dual R M)
    (x : M) : h x (H.toDualEquiv.symm φ) = φ x := by
  rw [← H.toDualEquiv_apply, LinearEquiv.apply_symm_apply]
def IsIsometry (h₁ : HermForm R M) (h₂ : HermForm R N) (f : M →ₗ[R] N) : Prop :=
  ∀ x y, h₂ (f x) (f y) = h₁ x y
theorem IsIsometry.id (h : HermForm R M) : h.IsIsometry h LinearMap.id := fun _ _ => rfl
theorem IsIsometry.comp {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}
    {g : N →ₗ[R] P} {f : M →ₗ[R] N} (hg : h₂.IsIsometry h₃ g) (hf : h₁.IsIsometry h₂ f) :
    h₁.IsIsometry h₃ (g ∘ₗ f) := fun x y => (hg _ _).trans (hf x y)
theorem IsIsometry.injective {h₁ : HermForm R M} {h₂ : HermForm R N} {f : M →ₗ[R] N}
    (hf : h₁.IsIsometry h₂ f) (H : h₁.Nondegenerate) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  exact fun x hx => H.eq_zero_left fun y => by rw [← hf, hx, zero_left]
structure IsometryEquiv (h₁ : HermForm R M) (h₂ : HermForm R N) extends M ≃ₗ[R] N where
  map_app' : ∀ x y, h₂ (toFun x) (toFun y) = h₁ x y
def Isometric (h₁ : HermForm R M) (h₂ : HermForm R N) : Prop := Nonempty (h₁.IsometryEquiv h₂)
namespace IsometryEquiv
variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}
instance : EquivLike (h₁.IsometryEquiv h₂) M N where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual
instance : LinearEquivClass (h₁.IsometryEquiv h₂) R M N where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv
@[simp] theorem coe_toLinearEquiv (f : h₁.IsometryEquiv h₂) : ⇑f.toLinearEquiv = f := rfl
@[simp] theorem coe_mk (e : M ≃ₗ[R] N) (he) : ⇑(⟨e, he⟩ : h₁.IsometryEquiv h₂) = e := rfl
@[ext] theorem ext {f g : h₁.IsometryEquiv h₂} (H : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ H
@[simp] theorem map_app (f : h₁.IsometryEquiv h₂) (x y : M) : h₂ (f x) (f y) = h₁ x y :=
  f.map_app' x y
@[refl] def refl (h : HermForm R M) : h.IsometryEquiv h :=
  ⟨LinearEquiv.refl R M, fun _ _ => rfl⟩
@[symm] def symm (f : h₁.IsometryEquiv h₂) : h₂.IsometryEquiv h₁ :=
  ⟨f.toLinearEquiv.symm, fun x y => by
    rw [← f.map_app]
    exact congrArg₂ (fun a b => h₂ a b) (f.toLinearEquiv.apply_symm_apply x)
      (f.toLinearEquiv.apply_symm_apply y)⟩
@[trans] def trans (f : h₁.IsometryEquiv h₂) (g : h₂.IsometryEquiv h₃) : h₁.IsometryEquiv h₃ :=
  ⟨f.toLinearEquiv.trans g.toLinearEquiv, fun x y => (g.map_app _ _).trans (f.map_app x y)⟩
@[simp] theorem refl_apply (h : HermForm R M) (x : M) : refl h x = x := rfl
@[simp] theorem trans_apply (f : h₁.IsometryEquiv h₂) (g : h₂.IsometryEquiv h₃) (x : M) :
    f.trans g x = g (f x) := rfl
@[simp] theorem apply_symm_apply (f : h₁.IsometryEquiv h₂) (x : N) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x
@[simp] theorem symm_apply_apply (f : h₁.IsometryEquiv h₂) (x : M) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x
@[simp] theorem symm_symm (f : h₁.IsometryEquiv h₂) : f.symm.symm = f := rfl
@[simp] theorem toLinearEquiv_symm (f : h₁.IsometryEquiv h₂) :
    f.symm.toLinearEquiv = f.toLinearEquiv.symm := rfl
theorem map_app_right (f : h₁.IsometryEquiv h₂) (x : N) (y : M) :
    h₂ x (f y) = h₁ (f.symm x) y := by rw [← f.map_app, apply_symm_apply]
theorem nondegenerate (f : h₁.IsometryEquiv h₂) (H : h₁.Nondegenerate) : h₂.Nondegenerate := by
  rw [nondegenerate_iff_left]
  intro x hx
  have : f.symm x = 0 := H.eq_zero_left fun y => by rw [← f.map_app_right, hx]
  simpa using congrArg f this
end IsometryEquiv
def comapIsometryEquiv (h : HermForm R M) (e : N ≃ₗ[R] M) :
    (h.comap e.toLinearMap).IsometryEquiv h := ⟨e, fun _ _ => rfl⟩
namespace Isometric
variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}
@[refl] theorem refl (h : HermForm R M) : h.Isometric h := ⟨.refl h⟩
@[symm] theorem symm (H : h₁.Isometric h₂) : h₂.Isometric h₁ := H.elim fun f => ⟨f.symm⟩
@[trans] theorem trans (H : h₁.Isometric h₂) (H' : h₂.Isometric h₃) : h₁.Isometric h₃ :=
  H.elim fun f => H'.elim fun g => ⟨f.trans g⟩
end Isometric
def unitaryGroup (h : HermForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' _ _ := rfl
  mul_mem' hg hg' x y := (hg _ _).trans (hg' x y)
  inv_mem' {g} hg x y := by
    rw [← hg]
    exact congrArg₂ (fun a b => h a b) (g.apply_symm_apply x) (g.apply_symm_apply y)
namespace unitaryGroup
theorem smul_def (g : h.unitaryGroup) (x : M) : g • x = (g : M ≃ₗ[R] M) x := rfl
@[simp] theorem map_app (g : h.unitaryGroup) (x y : M) :
    h ((g : M ≃ₗ[R] M) x) ((g : M ≃ₗ[R] M) y) = h x y := g.2 x y
@[simp] theorem smul_app (g : h.unitaryGroup) (x y : M) : h (g • x) (g • y) = h x y := g.2 x y
@[ext] theorem ext {g g' : h.unitaryGroup}
    (H : ∀ x, (g : M ≃ₗ[R] M) x = (g' : M ≃ₗ[R] M) x) : g = g' :=
  Subtype.ext (LinearEquiv.ext H)
def toIsometryEquiv (g : h.unitaryGroup) : h.IsometryEquiv h := ⟨g.1, g.2⟩
@[simp] theorem toIsometryEquiv_apply (g : h.unitaryGroup) (x : M) :
    toIsometryEquiv g x = (g : M ≃ₗ[R] M) x := rfl
variable (h) in

def toEnd : h.unitaryGroup →* Module.End R M where
  toFun g := (g : M ≃ₗ[R] M).toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl
@[simp] theorem toEnd_apply (g : h.unitaryGroup) (x : M) :
    toEnd h g x = (g : M ≃ₗ[R] M) x := rfl
end unitaryGroup
def IsometryEquiv.toUnitary (f : h.IsometryEquiv h) : h.unitaryGroup :=
  ⟨f.toLinearEquiv, f.map_app'⟩
@[simp] theorem IsometryEquiv.coe_toUnitary (f : h.IsometryEquiv h) :
    (f.toUnitary : M ≃ₗ[R] M) = f.toLinearEquiv := rfl
def IsometryEquiv.unitaryCongr {h₁ : HermForm R M} {h₂ : HermForm R N}
    (f : h₁.IsometryEquiv h₂) : h₁.unitaryGroup ≃* h₂.unitaryGroup where
  toFun g := (f.symm.trans ((unitaryGroup.toIsometryEquiv g).trans f)).toUnitary
  invFun g := (f.trans ((unitaryGroup.toIsometryEquiv g).trans f.symm)).toUnitary
  left_inv g := by ext; simp
  right_inv g := by ext; simp
  map_mul' g g' := by ext; simp
@[simp] theorem IsometryEquiv.unitaryCongr_apply {h₁ : HermForm R M} {h₂ : HermForm R N}
    (f : h₁.IsometryEquiv h₂) (g : h₁.unitaryGroup) (x : N) :
    (f.unitaryCongr g : N ≃ₗ[R] N) x = f ((g : M ≃ₗ[R] M) (f.symm x)) := rfl
@[simp] theorem IsometryEquiv.unitaryCongr_symm {h₁ : HermForm R M} {h₂ : HermForm R N}
    (f : h₁.IsometryEquiv h₂) : f.unitaryCongr.symm = f.symm.unitaryCongr := rfl
end Ring
section Field
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}
noncomputable def IsIsometry.toUnitary {f : V →ₗ[K] V} (hf : h.IsIsometry h f)
    (H : h.Nondegenerate) : h.unitaryGroup :=
  ⟨LinearEquiv.ofInjectiveEndo f (hf.injective H), hf⟩
@[simp] theorem IsIsometry.toUnitary_apply {f : V →ₗ[K] V} (hf : h.IsIsometry h f)
    (H : h.Nondegenerate) (x : V) : (hf.toUnitary H : V ≃ₗ[K] V) x = f x := rfl
end Field
section Complex
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : HermForm ℂ V)
@[simp] theorem im_apply_self (x : V) : (h x x).im = 0 :=
  Complex.conj_eq_iff_im.1 (h.conj_apply x x)
@[simp] theorem ofReal_re_apply_self (x : V) : ((h x x).re : ℂ) = h x x :=
  Complex.conj_eq_iff_re.1 (h.conj_apply x x)
def PosDef : Prop := ∀ x, x ≠ 0 → 0 < (h x x).re
def NegDef : Prop := ∀ x, x ≠ 0 → (h x x).re < 0
variable {h}
theorem PosDef.nondegenerate (H : h.PosDef) : h.Nondegenerate :=
  h.nondegenerate_iff_left.2 fun x hx => by
    by_contra hne
    simpa [hx x] using H x hne
theorem NegDef.nondegenerate (H : h.NegDef) : h.Nondegenerate :=
  h.nondegenerate_iff_left.2 fun x hx => by
    by_contra hne
    simpa [hx x] using H x hne
end Complex
end HermForm
universe u v
structure HermModule (R : Type u) [CommRing R] [StarRing R] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]

  form : HermForm R carrier
attribute [instance] HermModule.addCommGroup HermModule.module
instance (R : Type u) [CommRing R] [StarRing R] : CoeSort (HermModule.{u, v} R) (Type v) :=
  ⟨HermModule.carrier⟩
structure HermSpace (K : Type u) [Field K] [StarRing K] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finite : FiniteDimensional K carrier]

  form : HermForm K carrier
  nondegenerate : form.Nondegenerate
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
instance (K : Type u) [Field K] [StarRing K] : CoeSort (HermSpace.{u, v} K) (Type v) :=
  ⟨HermSpace.carrier⟩
instance {K : Type u} [Field K] [CharZero K] [StarRing K] (V : HermSpace.{u, v} K) :
    Module ℚ V := Module.compHom V (algebraMap ℚ K)
abbrev HermSpace.toHermModule {K : Type u} [Field K] [StarRing K] (V : HermSpace.{u, v} K) :
    HermModule.{u, v} K := ⟨V, V.form⟩
class IsStarFixed (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E] :
    Prop where
  star_algebraMap : ∀ a : F, star (algebraMap F E a) = algebraMap F E a
attribute [simp] IsStarFixed.star_algebraMap
section IsStarFixed
variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]
instance (priority := 100) IsStarFixed.of_trivialStar [StarRing F] [TrivialStar F]
    [StarModule F E] : IsStarFixed F E :=
  ⟨fun a => by rw [← algebraMap_star_comm, star_trivial]⟩
instance IsStarFixed.int {E : Type*} [CommRing E] [StarRing E] [Algebra ℤ E] : IsStarFixed ℤ E :=
  ⟨fun a => by simp⟩
instance IsStarFixed.rat {E : Type*} [CommRing E] [StarRing E] [Algebra ℚ E] : IsStarFixed ℚ E :=
  ⟨fun a => DFunLike.congr_fun
    (Subsingleton.elim ((starRingEnd E).comp (algebraMap ℚ E)) (algebraMap ℚ E)) a⟩
theorem IsStarFixed.of_isScalarTower (F₀ : Type*) [CommSemiring F₀] [Algebra F₀ F] [Algebra F₀ E]
    [IsScalarTower F₀ F E] [IsStarFixed F E] : IsStarFixed F₀ E :=
  ⟨fun a => by rw [IsScalarTower.algebraMap_apply F₀ F E, IsStarFixed.star_algebraMap]⟩
variable [IsStarFixed F E]
def starAlgEquiv : E ≃ₐ[F] E :=
  { (starRingAut : RingAut E) with commutes' := IsStarFixed.star_algebraMap }
@[simp] theorem starAlgEquiv_apply (x : E) : starAlgEquiv F E x = star x := rfl
@[simp] theorem starAlgEquiv_symm : (starAlgEquiv F E).symm = starAlgEquiv F E := rfl
variable {F E}
end IsStarFixed
theorem starModule_of_algebraMap {R S : Type*} [CommSemiring R] [CommSemiring S] [StarRing R]
    [StarRing S] [Algebra R S] (hφ : ∀ x, algebraMap R S (star x) = star (algebraMap R S x)) :
    StarModule R S :=
  ⟨fun r s => by rw [Algebra.smul_def, Algebra.smul_def, star_mul', hφ]⟩
def StarTensor (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E]
    [Algebra F A] : Type _ := E ⊗[F] A
namespace StarTensor
section NoStar
variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
noncomputable instance : CommRing (StarTensor F E A) := inferInstanceAs (CommRing (E ⊗[F] A))
noncomputable instance (priority := 900) leftAlgebra (S : Type*) [CommSemiring S] [Algebra S E]
    [SMulCommClass F S E] : Algebra S (StarTensor F E A) :=
  inferInstanceAs (Algebra S (E ⊗[F] A))
noncomputable instance (priority := 800) rightAlgebra : Algebra A (StarTensor F E A) :=
  Algebra.TensorProduct.rightAlgebra (R := F) (A := E) (B := A)
instance (S T : Type*) [CommSemiring S] [CommSemiring T] [Algebra S E] [Algebra T E]
    [SMulCommClass F S E] [SMulCommClass F T E] [SMul S T] [IsScalarTower S T E] :
    IsScalarTower S T (StarTensor F E A) :=
  inferInstanceAs (IsScalarTower S T (E ⊗[F] A))
instance : IsScalarTower F A (StarTensor F E A) :=
  Algebra.TensorProduct.right_isScalarTower (R := F) (A := E) (B := A)
instance (S : Type*) [CommSemiring S] [Algebra S E] [SMulCommClass F S E] :
    SMulCommClass S A (StarTensor F E A) :=
  ⟨fun s a x => by simp only [Algebra.smul_def, mul_left_comm]⟩
instance (S : Type*) [CommSemiring S] [Algebra S E] [SMulCommClass F S E] :
    SMulCommClass A S (StarTensor F E A) := SMulCommClass.symm _ _ _
noncomputable def toTensor : StarTensor F E A ≃ₐ[E] E ⊗[F] A := AlgEquiv.refl
variable {E A} in

noncomputable def tmul (e : E) (a : A) : StarTensor F E A := e ⊗ₜ[F] a
variable {F E A}
@[simp] theorem toTensor_tmul (e : E) (a : A) : toTensor F E A (tmul F e a) = e ⊗ₜ[F] a := rfl
@[simp] theorem toTensor_symm_tmul (e : E) (a : A) :
    (toTensor F E A).symm (e ⊗ₜ[F] a) = tmul F e a := rfl
theorem algebraMap_left (e : E) : algebraMap E (StarTensor F E A) e = tmul F e 1 := rfl
theorem algebraMap_right (a : A) : algebraMap A (StarTensor F E A) a = tmul F 1 a := rfl
@[simp] theorem tmul_mul_tmul (e e' : E) (a a' : A) :
    tmul F e a * tmul F e' a' = tmul F (e * e') (a * a') :=
  Algebra.TensorProduct.tmul_mul_tmul e e' a a'
@[simp] theorem zero_tmul (a : A) : tmul F (0 : E) a = 0 := TensorProduct.zero_tmul E a
@[simp] theorem tmul_zero (e : E) : tmul F e (0 : A) = 0 := TensorProduct.tmul_zero A e
@[simp] theorem left_smul_tmul (c e : E) (a : A) : c • tmul F e a = tmul F (c * e) a := by
  simp [Algebra.smul_def, algebraMap_left]
@[simp] theorem right_smul_tmul (c : A) (e : E) (a : A) : c • tmul F e a = tmul F e (c * a) := by
  simp [Algebra.smul_def, algebraMap_right]
@[elab_as_elim]
theorem induction_on {motive : StarTensor F E A → Prop} (x : StarTensor F E A)
    (zero : motive 0) (tmul : ∀ e a, motive (tmul F e a))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  TensorProduct.induction_on (motive := motive) x zero tmul add
instance isPushout : Algebra.IsPushout F E A (StarTensor F E A) :=
  TensorProduct.isPushout (R := F) (S := E) (T := A)
instance isPushout' : Algebra.IsPushout F A E (StarTensor F E A) :=
  Algebra.IsPushout.symm inferInstance
variable (F E A) in

noncomputable def commRight : StarTensor F E A ≃ₐ[A] A ⊗[F] E :=
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := E) (B := A)
  (Algebra.TensorProduct.commRight F A E).symm
@[simp] theorem commRight_tmul (e : E) (a : A) : commRight F E A (tmul F e a) = a ⊗ₜ[F] e := rfl
@[simp] theorem commRight_symm_tmul (e : E) (a : A) :
    (commRight F E A).symm (a ⊗ₜ[F] e) = tmul F e a := rfl
instance [Module.Free F E] : Module.Free A (StarTensor F E A) :=
  .of_equiv (commRight F E A).symm.toLinearEquiv
instance [Module.Finite F E] : Module.Finite A (StarTensor F E A) :=
  .equiv (commRight F E A).symm.toLinearEquiv
instance [Module.Flat F E] : Module.Flat A (StarTensor F E A) :=
  .of_linearEquiv (commRight F E A).toLinearEquiv
instance [Module.Free F A] : Module.Free E (StarTensor F E A) :=
  inferInstanceAs (Module.Free E (E ⊗[F] A))
instance [Module.Finite F A] : Module.Finite E (StarTensor F E A) :=
  inferInstanceAs (Module.Finite E (E ⊗[F] A))
instance [Module.Flat F A] : Module.Flat E (StarTensor F E A) :=
  inferInstanceAs (Module.Flat E (E ⊗[F] A))
theorem algebraMap_left_injective [Module.Flat F E] (hA : Function.Injective (algebraMap F A)) :
    Function.Injective (algebraMap E (StarTensor F E A)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) hA
variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]
variable (E) in

noncomputable def map (f : A →ₐ[F] B) : StarTensor F E A →ₐ[E] StarTensor F E B :=
  Algebra.TensorProduct.map (AlgHom.id E E) f
@[simp] theorem map_tmul (f : A →ₐ[F] B) (e : E) (a : A) :
    map E f (tmul F e a) = tmul F e (f a) := rfl
@[simp] theorem map_algebraMap_right (f : A →ₐ[F] B) (a : A) :
    map E f (algebraMap A _ a) = algebraMap B _ (f a) := rfl
@[simp] theorem map_id : map E (AlgHom.id F A) = AlgHom.id E _ :=
  Algebra.TensorProduct.map_id
noncomputable def lift {D : Type*} [CommRing D] (f : E →+* D) (g : A →+* D)
    (hfg : ∀ c : F, f (algebraMap F E c) = g (algebraMap F A c)) : StarTensor F E A →+* D :=
  letI := (f.comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.lift (⟨f, fun _ => rfl⟩ : E →ₐ[F] D)
    (⟨g, fun c => (hfg c).symm⟩ : A →ₐ[F] D) fun _ _ => Commute.all _ _).toRingHom
@[simp] theorem lift_tmul {D : Type*} [CommRing D] (f : E →+* D) (g : A →+* D) (hfg) (e : E)
    (a : A) : lift f g hfg (tmul F e a) = f e * g a := rfl
@[simp] theorem lift_algebraMap_left {D : Type*} [CommRing D] (f : E →+* D) (g : A →+* D) (hfg)
    (e : E) : lift f g hfg (algebraMap E (StarTensor F E A) e) = f e := by
  simp [algebraMap_left]
@[simp] theorem lift_algebraMap_right {D : Type*} [CommRing D] (f : E →+* D) (g : A →+* D) (hfg)
    (a : A) : lift f g hfg (algebraMap A (StarTensor F E A) a) = g a := by
  simp [algebraMap_right]
variable (F E) in

noncomputable def rid : StarTensor F E F ≃ₐ[E] E := Algebra.TensorProduct.rid F E E
@[simp] theorem rid_tmul (e : E) (a : F) : rid F E (tmul F e a) = a • e := rfl
end NoStar
section Star
variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]
variable (F E A) in

noncomputable def conjHom : StarTensor F E A →ₐ[F] StarTensor F E A :=
  Algebra.TensorProduct.map (starAlgEquiv F E).toAlgHom (AlgHom.id F A)
@[simp] theorem conjHom_tmul (e : E) (a : A) : conjHom F E A (tmul F e a) = tmul F (star e) a :=
  rfl
noncomputable instance : StarRing (StarTensor F E A) where
  star := conjHom F E A
  star_involutive x := x.induction_on (by simp) (by simp)
    (fun x y hx hy => by rw [map_add, map_add, hx, hy])
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y
@[simp] theorem star_tmul (e : E) (a : A) : star (tmul F e a) = tmul F (star e) a := rfl
instance : IsStarFixed A (StarTensor F E A) :=
  ⟨fun a => by rw [algebraMap_right, star_tmul, star_one]⟩
instance (S : Type*) [CommSemiring S] [Algebra S E] [SMulCommClass F S E] [IsStarFixed S E] :
    IsStarFixed S (StarTensor F E A) :=
  ⟨fun s => congrArg (fun e => tmul F e (1 : A)) (IsStarFixed.star_algebraMap s)⟩
instance (S : Type*) [CommSemiring S] [StarRing S] [Algebra S E] [SMulCommClass F S E]
    [StarModule S E] : StarModule S (StarTensor F E A) :=
  starModule_of_algebraMap fun s => congrArg (fun e => tmul F e (1 : A)) (algebraMap_star_comm s)
@[simp] theorem star_algebraMap_left (e : E) :
    star (algebraMap E (StarTensor F E A) e) = algebraMap E _ (star e) := rfl
variable {B : Type*} [CommRing B] [Algebra F B]
end Star
end StarTensor
section RingOfIntegers
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
instance (priority := 100) ringOfIntegersModule : Module (𝓞 K) V :=
  inferInstanceAs (Module (integralClosure ℤ K) V)
instance (priority := 100) ringOfIntegersIsScalarTower : IsScalarTower (𝓞 K) K V :=
  inferInstanceAs (IsScalarTower (integralClosure ℤ K) K V)
instance (priority := 100) (L : Type*) [Ring L] [Algebra K L] [Module L V] [IsScalarTower K L V] :
    IsScalarTower (𝓞 K) L V :=
  ⟨fun a b x => smul_assoc (a : K) b x⟩
instance (priority := 100) (L : Type*) [Field L] [Algebra K L] [Module L V]
    [IsScalarTower K L V] : IsScalarTower (𝓞 K) (𝓞 L) V :=
  .of_algebraMap_smul fun a x => algebraMap_smul L (a : K) x
end RingOfIntegers
section CM
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
instance : IsStarFixed (maximalRealSubfield E) E := ⟨(IsCMField.complexConj E).commutes⟩
variable {E}
@[simp] theorem complexEmbedding_star (τ : E →+* ℂ) (x : E) : τ (star x) = star (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x
noncomputable instance : StarRing (𝓞 E) where
  star := IsCMField.ringOfIntegersComplexConj E
  star_involutive x := RingOfIntegers.ext (star_star (x : E))
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y
instance : StarModule (𝓞 E) E := starModule_of_algebraMap fun _ => rfl
instance {L : Type*} [CommRing L] [StarRing L] [Algebra E L] [StarModule E L] :
    StarModule (𝓞 E) L :=
  starModule_of_algebraMap fun x => algebraMap_star_comm (x : E)
instance : IsStarFixed (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  ⟨(IsCMField.ringOfIntegersComplexConj E).commutes⟩
instance {K L : Type*} [Field K] [CommRing L] [StarRing L] [Algebra K L] [IsStarFixed K L] :
    IsStarFixed (𝓞 K) L :=
  .of_isScalarTower K L (𝓞 K)
variable (E) in

abbrev CMTensor (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A] : Type _ :=
  StarTensor (maximalRealSubfield E) E A
namespace CMTensor
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]
instance : IsScalarTower (maximalRealSubfield E) A (CMTensor E A) :=
  .of_algebraMap_eq fun c =>
    @IsScalarTower.algebraMap_apply _ A (CMTensor E A) _ _ _ _ _
      (StarTensor.leftAlgebra _ E A _) _ c
instance : IsStarFixed (maximalRealSubfield E) (CMTensor E A) :=
  .of_isScalarTower A _ _
instance (V : Type*) [AddCommGroup V] [Module E V] :
    IsScalarTower (maximalRealSubfield E) A (CMTensor E A ⊗[E] V) :=
  .of_algebraMap_smul fun c x => by
    rw [← algebraMap_smul (CMTensor E A) (algebraMap _ A c), ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
instance isPushout : Algebra.IsPushout (maximalRealSubfield E) E A (CMTensor E A) :=
  StarTensor.isPushout
instance isPushout' : Algebra.IsPushout (maximalRealSubfield E) A E (CMTensor E A) :=
  StarTensor.isPushout'
theorem algebraMap_left_injective [Nontrivial A] :
    Function.Injective (algebraMap E (CMTensor E A)) :=
  StarTensor.algebraMap_left_injective (RingHom.injective _)
instance [Nontrivial A] : Nontrivial (CMTensor E A) :=
  (algebraMap_left_injective (E := E) (A := A)).nontrivial
end CMTensor
end CM
end GlobalTheory


