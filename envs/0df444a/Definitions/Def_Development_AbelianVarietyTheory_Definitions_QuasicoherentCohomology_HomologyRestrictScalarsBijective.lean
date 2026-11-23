-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:00.761307+00:00
-- url     : https://prove2.me/theorems/e260199d-49ec-4e27-8f8d-6fe6954a5ef6
-- title:
--   Homology Restrict Scalars Bijective
-- statement:
--   Definitions and structural lemmas for Homology Restrict Scalars Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HomologyRestrictScalarsBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cechCyclesIso_hom_subtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
namespace GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
def cechClass (A : Cube.{v} ι R) (p : ℕ) :
    LinearMap.ker (Cube.d A (p + 1)) →ₗ[R] (cechComplex A).homology p :=
  ((cechCyclesIso A p).inv ≫ (cechComplex A).homologyπ p).hom
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.iCycles_cechCyclesIso_inv (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1))) :
    ((_root_.GlobalTheory.cechComplex A).iCycles p).hom ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = x.1 := by
  have e : (_root_.GlobalTheory.cechCyclesIso A p).hom.hom
      ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = x := by
    simp
  rw [← _root_.GlobalTheory.cechCyclesIso_hom_subtype]
  change ((_root_.GlobalTheory.cechCyclesIso A p).hom.hom
    ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x)).1 = x.1
  rw [e]
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_surjective (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ) :
    Function.Surjective (_root_.GlobalTheory.cechClass A p) :=
  (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((_root_.GlobalTheory.cechCyclesIso A p).inv ≫ (_root_.GlobalTheory.cechComplex A).homologyπ p))
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_succ_eq_zero_iff (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1 + 1))) :
    _root_.GlobalTheory.cechClass A (p + 1) x = 0 ↔
      ∃ y, _root_.GlobalTheory.Cube.d A (p + 1) y = x.1 := by
  set K := _root_.GlobalTheory.cechComplex A
  have hex : (ShortComplex.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1)) (by simp)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel p (p + 1) (by simp))
  have hrange : LinearMap.range (K.toCycles p (p + 1)).hom =
      LinearMap.ker (K.homologyπ (p + 1)).hom := hex.moduleCat_range_eq_ker
  have hi : Function.Injective (K.iCycles (p + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hd : ∀ y, (K.iCycles (p + 1)).hom ((K.toCycles p (p + 1)).hom y) =
      _root_.GlobalTheory.Cube.d A (p + 1) y := by
    intro y
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.toCycles_i,
      _root_.GlobalTheory.cechComplex_d]
    rfl
  change (K.homologyπ (p + 1)).hom ((_root_.GlobalTheory.cechCyclesIso A (p + 1)).inv.hom x) = 0 ↔ _
  rw [← LinearMap.mem_ker, ← hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have := congrArg (K.iCycles (p + 1)).hom hy
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv, hd] at this
    exact this
  · rintro ⟨y, hy⟩
    refine ⟨y, hi ?_⟩
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv]
    exact (hd y).trans hy
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
theorem cechClass_zero_eq_iso_inv (A : _root_.GlobalTheory.Cube.{v} ι R) :
    _root_.GlobalTheory.cechClass A 0 = (_root_.GlobalTheory.cechHomologyZeroIso A).inv.hom := by
  have e : (_root_.GlobalTheory.cechCyclesIso A 0).inv ≫ (_root_.GlobalTheory.cechComplex A).homologyπ 0 =
      (_root_.GlobalTheory.cechHomologyZeroIso A).inv := by
    rw [Iso.inv_comp_eq, ← _root_.GlobalTheory.homologyπ_cechHomologyZeroIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [_root_.GlobalTheory.cechClass, e]
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
theorem cechClass_zero_bijective' (A : _root_.GlobalTheory.Cube.{v} ι R) :
    Function.Bijective (_root_.GlobalTheory.cechClass A 0) := by
  rw [cechClass_zero_eq_iso_inv]
  exact (_root_.GlobalTheory.cechHomologyZeroIso A).symm.toLinearEquiv.bijective
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_zero_eq_zero_iff (A : _root_.GlobalTheory.Cube.{v} ι R)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (0 + 1))) :
    _root_.GlobalTheory.cechClass A 0 x = 0 ↔ x = 0 :=
  (cechClass_zero_bijective' A).1.eq_iff' (map_zero _)
structure Cube.SemiHom (f : R →+* S) (A : Cube.{v} ι R) (B : Cube.{v'} ι S) where

  app : ∀ s, A.obj s →ₛₗ[f] B.obj s

  app_res : ∀ {s t : Finset ι} (h : s ⊆ t) (x : A.obj s),
    app t (Cube.res A h x) = Cube.res B h (app s x)
namespace Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)
omit [LinearOrder ι] in

@[simps]
def ofHom (φ : A ⟶ A') : Cube.SemiHom (RingHom.id R) A A' where
  app s := (φ.app s).hom
  app_res := Cube.app_res φ
omit [LinearOrder ι] in

def term (p : ℕ) : Cube.Term A p →ₛₗ[f] Cube.Term B p where
  toFun x s := ψ.app s.1 (x s)
  map_add' x y := funext fun s => map_add _ _ _
  map_smul' r x := funext fun s => map_smulₛₗ (ψ.app s.1) r (x s)
omit [LinearOrder ι] in

@[simp]
theorem term_apply (p : ℕ) (x : Cube.Term A p) (s : {s : Finset ι // s.card = p}) :
    ψ.term p x s = ψ.app s.1 (x s) := rfl
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.term_d (p : ℕ) (x : _root_.GlobalTheory.Cube.Term A p) :
    ψ.term (p + 1) (_root_.GlobalTheory.Cube.d A p x) =
      _root_.GlobalTheory.Cube.d B p (ψ.term p x) := by
  funext t
  rw [_root_.GlobalTheory.Cube.SemiHom.term_apply, _root_.GlobalTheory.Cube.d_apply,
    _root_.GlobalTheory.Cube.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, _root_.GlobalTheory.Cube.SemiHom.app_res, _root_.GlobalTheory.Cube.SemiHom.term_apply]
def cocycle (p : ℕ) : LinearMap.ker (Cube.d A p) →ₛₗ[f] LinearMap.ker (Cube.d B p) :=
  ((ψ.term p).domRestrict _).codRestrict _ fun x => by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, ← term_d, x.2, map_zero]
@[simp]
theorem coe_cocycle (p : ℕ) (x : LinearMap.ker (Cube.d A p)) :
    (ψ.cocycle p x).1 = ψ.term p x.1 := rfl
open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.cechClass_cocycle_eq_zero (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)))
    (h : _root_.GlobalTheory.cechClass A p x = 0) :
    _root_.GlobalTheory.cechClass B p (ψ.cocycle (p + 1) x) = 0 := by
  cases p with
  | zero =>
    rw [_root_.GlobalTheory.cechClass_zero_eq_zero_iff] at h ⊢
    rw [h, map_zero]
  | succ p =>
    rw [_root_.GlobalTheory.cechClass_succ_eq_zero_iff] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨ψ.term (p + 1) y, by rw [← _root_.GlobalTheory.Cube.SemiHom.term_d, hy, _root_.GlobalTheory.Cube.SemiHom.coe_cocycle]⟩
def homology (p : ℕ) : (cechComplex A).homology p →ₛₗ[f] (cechComplex B).homology p :=
  ((LinearMap.ker (cechClass A p)).liftQ ((cechClass B p).comp (ψ.cocycle (p + 1)))
    (ψ.cechClass_cocycle_eq_zero p)).comp
    ((cechClass A p).quotKerEquivOfSurjective (cechClass_surjective A p)).symm.toLinearMap
omit [LinearOrder ι] in

def restrictScalars (f : R →+* S) (B : Cube.{v} ι S) :
    Cube.SemiHom f (B ⋙ ModuleCat.restrictScalars f) B where
  app s := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  app_res _ _ := rfl
omit [LinearOrder ι] in

def constRingHom (ι : Type) (f : R →+* S) :
    Cube.SemiHom f (Cube.const ι (ModuleCat.of R R)) (Cube.const ι (ModuleCat.of S S)) where
  app _ := f.toSemilinearMap
  app_res _ _ := rfl
example (s : {s : Finset (Fin 2) // s.card = 1}) :
    (constRingHom (Fin 2) (Int.castRingHom ℚ)).term 1 (fun _ => (2 : ℤ)) s = (2 : ℚ) := rfl
end Cube.SemiHom
end GlobalTheory


