-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2f89986c-ba4f-5d33-9975-611c0087db65

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlueFromBasisSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (B : Set V.affineOpens)

structure GData where
  hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B
  hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1
  M : ↥B → Type u
  [acg : ∀ W, AddCommGroup (M W)]
  [mR : ∀ W, Module R (M W)]
  [mΓ : ∀ W, Module Γ(V, W.1.1) (M W)]
  [tower : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1; IsScalarTower R Γ(V, W.1.1) (M W)]
  res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[R] M W')
  res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(V, W.1.1)) (x : M W),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x
  res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x
  res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
    res (h.trans h') x = res h (res h' x)
  hqc : ∀ (W Wg : ↥B) (g : Γ(V, W.1.1)) (hWg : Wg.1.1 = V.basicOpen g),
    (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
        res (hWg.trans_le (V.basicOpen_le g)) x =
          (V.presheaf.map (homOfLE (hWg.trans_le (V.basicOpen_le g))).op).hom (g ^ n) • y) ∧
    (∀ x : M W, res (hWg.trans_le (V.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0)
  hfg : ∀ W : ↥B, Module.Finite (Γ(V, W.1.1) : Type u) (M W)

attribute [scoped instance] GData.acg GData.mR GData.mΓ GData.tower

variable {π B} (D : GData π B)

namespace GData

theorem res_res {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : D.M W) :
    D.res h (D.res h' x) = D.res (h.trans h') x := (D.res_comp h h' x).symm

theorem res_congr {W W' : ↥B} (h h' : W'.1.1 ≤ W.1.1) (x : D.M W) : D.res h x = D.res h' x := rfl

def bo (W : ↥B) (g : Γ(V, W.1.1)) : ↥B :=
  ⟨⟨V.basicOpen g, W.1.2.basicOpen g⟩, D.hdown W.1 _ (V.basicOpen_le g) W.2⟩

theorem bo_coe (W : ↥B) (g : Γ(V, W.1.1)) : (D.bo W g).1.1 = V.basicOpen g := rfl

theorem bo_le (W : ↥B) (g : Γ(V, W.1.1)) : (D.bo W g).1.1 ≤ W.1.1 := V.basicOpen_le g

abbrev Mem (U : V.Opens) : Type u := {W : ↥B // W.1.1 ≤ U}

def fam (U : V.Opens) : Submodule R (∀ W : Mem (B := B) U, D.M W.1) where
  carrier := {t | ∀ (W W' : Mem (B := B) U) (h : W'.1.1.1 ≤ W.1.1.1), D.res h (t W) = t W'}
  add_mem' {s t} hs ht W W' h := by
    show D.res h (s W + t W) = s W' + t W'
    rw [map_add, hs W W' h, ht W W' h]
  zero_mem' W W' h := by show D.res h 0 = 0; exact map_zero _
  smul_mem' r {t} ht W W' h := by
    show D.res h (r • t W) = r • t W'
    rw [map_smul, ht W W' h]

theorem mem_fam_iff (U : V.Opens) (t : ∀ W : Mem (B := B) U, D.M W.1) :
    t ∈ D.fam U ↔ ∀ (W W' : Mem (B := B) U) (h : W'.1.1.1 ≤ W.1.1.1), D.res h (t W) = t W' := Iff.rfl

abbrev toMem (U : V.Opens) (W : Mem (B := B) U) : Γ(V, U) ⟶ Γ(V, W.1.1.1) := V.presheaf.map (homOfLE W.2).op

theorem toMem_algebraMap (U : V.Opens) (W : Mem (B := B) U) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1.1
    (toMem U W).hom (algebraMap R Γ(V, U) r) = algebraMap R Γ(V, W.1.1.1) r := by
  show (V.presheaf.map _).hom ((π.appLE ⊤ U le_top).hom _) = (π.appLE ⊤ W.1.1.1 le_top).hom _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_toMem (U : V.Opens) (W W' : Mem (B := B) U) (h : W'.1.1.1 ≤ W.1.1.1) (a : Γ(V, U)) :
    (V.presheaf.map (homOfLE h).op).hom ((toMem U W).hom a) = (toMem U W').hom a := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

@[reducible] def famSMul (U : V.Opens) : SMul Γ(V, U) (D.fam U) where
  smul a t := ⟨fun W => (toMem U W).hom a • t.1 W, by
    intro W W' h
    show D.res h ((toMem U W).hom a • t.1 W) = (toMem U W').hom a • t.1 W'
    rw [D.res_smul, map_toMem, t.2 W W' h]⟩

@[reducible] def famModule (U : V.Opens) : Module Γ(V, U) (D.fam U) :=
  letI := D.famSMul U
  { one_smul := fun t => Subtype.ext (funext fun W => by
      show (toMem U W).hom 1 • t.1 W = t.1 W
      rw [map_one, one_smul])
    mul_smul := fun a b t => Subtype.ext (funext fun W => by
      show (toMem U W).hom (a * b) • t.1 W = (toMem U W).hom a • ((toMem U W).hom b • t.1 W)
      rw [map_mul, mul_smul])
    smul_zero := fun a => Subtype.ext (funext fun W => smul_zero _)
    smul_add := fun a s t => Subtype.ext (funext fun W => smul_add _ _ _)
    add_smul := fun a b t => Subtype.ext (funext fun W => by
      show (toMem U W).hom (a + b) • t.1 W = (toMem U W).hom a • t.1 W + (toMem U W).hom b • t.1 W
      rw [map_add, add_smul])
    zero_smul := fun t => Subtype.ext (funext fun W => by
      show (toMem U W).hom 0 • t.1 W = 0
      rw [map_zero, zero_smul]) }

def famRes {U U' : V.Opens} (h : U ≤ U') : D.fam U' →ₗ[R] D.fam U where
  toFun t := ⟨fun W => t.1 ⟨W.1, W.2.trans h⟩, fun W W' h' => t.2 ⟨W.1, W.2.trans h⟩ ⟨W'.1, W'.2.trans h⟩ h'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def G : OModulePresheaf π where
  obj U := D.fam U
  module U := inferInstance
  moduleSections U := D.famModule U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := D.famModule U
    refine ⟨fun r a t => Subtype.ext (funext fun W => ?_)⟩
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1.1
    show (toMem U W).hom (r • a) • t.1 W = r • ((toMem U W).hom a • t.1 W)
    rw [Algebra.smul_def, map_mul, mul_smul, toMem_algebraMap, algebraMap_smul]
  res h := D.famRes h
  res_smul {U U'} h a t := Subtype.ext (funext fun W => by
    show (toMem U' ⟨W.1, W.2.trans h⟩).hom a • t.1 ⟨W.1, W.2.trans h⟩ =
      (toMem U W).hom ((V.presheaf.map (homOfLE h).op).hom a) • t.1 ⟨W.1, W.2.trans h⟩
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), ← V.presheaf.map_comp]; rfl)
  res_refl U := LinearMap.ext fun t => Subtype.ext (funext fun W => rfl)
  res_comp h h' := LinearMap.ext fun t => Subtype.ext (funext fun W => rfl)

theorem G_obj (U : V.Opens) : D.G.obj U = ↥(D.fam U) := rfl

theorem G_res_coe {U U' : V.Opens} (h : U ≤ U') (t : D.G.obj U') (W : Mem (B := B) U) :
    (D.G.res h t).1 W = t.1 ⟨W.1, W.2.trans h⟩ := rfl

theorem G_smul_coe (U : V.Opens) (a : Γ(V, U)) (t : D.G.obj U) (W : Mem (B := B) U) :
    (a • t).1 W = (toMem U W).hom a • t.1 W := rfl

theorem G_ext {U : V.Opens} {s t : D.G.obj U} (h : ∀ W : Mem (B := B) U, s.1 W = t.1 W) : s = t :=
  Subtype.ext (funext h)

def ev (W : ↥B) : D.G.obj W.1.1 →ₗ[R] D.M W where
  toFun t := t.1 ⟨W, le_rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lf (W : ↥B) : D.M W →ₗ[R] D.G.obj W.1.1 where
  toFun x := ⟨fun W' => D.res W'.2 x, fun W₁ W₂ h => D.res_res h W₁.2 x⟩
  map_add' x y := Subtype.ext (funext fun W' => map_add _ x y)
  map_smul' r x := Subtype.ext (funext fun W' => LinearMap.map_smul _ r x)

theorem ev_lf (W : ↥B) (x : D.M W) : D.ev W (D.lf W x) = x := D.res_refl W x

theorem lf_ev (W : ↥B) (t : D.G.obj W.1.1) : D.lf W (D.ev W t) = t :=
  D.G_ext fun W' => t.2 ⟨W, le_rfl⟩ W' W'.2

def e (W : ↥B) : D.G.obj W.1.1 ≃ₗ[R] D.M W :=
  LinearEquiv.ofLinear (D.ev W) (D.lf W) (LinearMap.ext (D.ev_lf W)) (LinearMap.ext (D.lf_ev W))

theorem e_apply (W : ↥B) (t : D.G.obj W.1.1) : D.e W t = t.1 ⟨W, le_rfl⟩ := rfl

theorem e_symm_apply_coe (W : ↥B) (x : D.M W) (W' : Mem (B := B) W.1.1) : ((D.e W).symm x).1 W' = D.res W'.2 x := rfl

theorem e_smul (W : ↥B) (a : Γ(V, W.1.1)) (t : D.G.obj W.1.1) : D.e W (a • t) = a • D.e W t := by
  show (V.presheaf.map (homOfLE (le_refl W.1.1)).op).hom a • t.1 ⟨W, le_rfl⟩ = a • t.1 ⟨W, le_rfl⟩
  rw [Subsingleton.elim (homOfLE (le_refl W.1.1)).op (𝟙 (op W.1.1)), V.presheaf.map_id]; rfl

theorem e_res (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (t : D.G.obj W.1.1) :
    D.e W' (D.G.res h t) = D.res h (D.e W t) :=
  (t.2 ⟨W, le_rfl⟩ ⟨W', h⟩ h).symm

theorem coe_eq_e_res {U : V.Opens} (t : D.G.obj U) (W : Mem (B := B) U) :
    t.1 W = D.e W.1 (D.G.res W.2 t) := rfl

end GData

end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol"

namespace GlueFromBasisSol
namespace GData

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}
variable (D : GData π B)

def MO (O : V.Opens) (W : Mem (B := B) O) : Type u := D.M W.1

scoped instance instACG_MO (O : V.Opens) (W : Mem (B := B) O) : AddCommGroup (D.MO O W) :=
  inferInstanceAs (AddCommGroup (D.M W.1))
scoped instance instMod_MO (O : V.Opens) (W : Mem (B := B) O) : Module Γ(V, O) (D.MO O W) :=
  Module.compHom (D.M W.1) (toMem O W).hom

theorem MO_smul_def (O : V.Opens) (W : Mem (B := B) O) (a : Γ(V, O)) (x : D.MO O W) :
    a • x = (show D.MO O W from (toMem O W).hom a • (show D.M W.1 from x)) := rfl

def resO (O : V.Opens) {W W' : Mem (B := B) O} (h : W'.1.1.1 ≤ W.1.1.1) : D.MO O W →ₗ[Γ(V, O)] D.MO O W' where
  toFun x := (show D.MO O W' from D.res h (show D.M W.1 from x))
  map_add' x y := map_add (D.res h) _ _
  map_smul' a x := by
    show D.res h ((toMem O W).hom a • (show D.M W.1 from x)) = (toMem O W').hom a • D.res h _
    rw [D.res_smul, map_toMem]

theorem resO_apply (O : V.Opens) {W W' : Mem (B := B) O} (h : W'.1.1.1 ≤ W.1.1.1) (x : D.MO O W) :
    D.resO O h x = (show D.MO O W' from D.res h (show D.M W.1 from x)) := rfl

theorem resO_resO (O : V.Opens) {W W' W'' : Mem (B := B) O} (h : W'.1.1.1 ≤ W.1.1.1) (h' : W''.1.1.1 ≤ W'.1.1.1)
    (x : D.MO O W) : D.resO O h' (D.resO O h x) = D.resO O (h'.trans h) x :=
  D.res_res h' h _

def boO (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) : Mem (B := B) O :=
  ⟨D.bo W.1 ((toMem O W).hom g), (D.bo_le W.1 _).trans W.2⟩

theorem boO_coe (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) :
    (D.boO O W g).1.1.1 = V.basicOpen ((toMem O W).hom g) := rfl

theorem boO_le (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) : (D.boO O W g).1.1.1 ≤ W.1.1.1 :=
  V.basicOpen_le _

theorem boO_coe' (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) :
    (D.boO O W g).1.1.1 = W.1.1.1 ⊓ V.basicOpen g := by
  rw [boO_coe]; exact V.basicOpen_res g (homOfLE W.2).op

theorem toMem_boO (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) (a : Γ(V, O)) :
    (toMem O (D.boO O W g)).hom a =
      (V.presheaf.map (homOfLE (D.boO_le O W g)).op).hom ((toMem O W).hom a) :=
  (map_toMem O W (D.boO O W g) (D.boO_le O W g) a).symm

theorem isLocalizedModule_resO (O : V.Opens) (W : Mem (B := B) O) (g : Γ(V, O)) :
    IsLocalizedModule (Submonoid.powers g) (D.resO O (D.boO_le O W g)) := by
  have hq := D.hqc W.1 (D.boO O W g).1 ((toMem O W).hom g) rfl

  have hunit : IsUnit ((toMem O (D.boO O W g)).hom g) := by
    rw [D.toMem_boO]
    exact V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen ((toMem O W).hom g)
  have hgn : ∀ n : ℕ, (toMem O W).hom (g ^ n) = ((toMem O W).hom g) ^ n := fun n => map_pow _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((toMem O (D.boO O W g)).hom (g ^ n)) := by rw [map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : D.M (D.boO O W g).1 => (toMem O (D.boO O W g)).hom (g ^ n) • y) :=
      hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    refine ⟨(x, ⟨g ^ n, n, rfl⟩), ?_⟩
    show (toMem O (D.boO O W g)).hom (g ^ n) • (show D.M (D.boO O W g).1 from y) = D.res _ x
    rw [D.toMem_boO, hgn, hx]
  · intro x₁ x₂ h
    have h0 : D.res (D.boO_le O W g) ((show D.M W.1 from x₁) - (show D.M W.1 from x₂)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (toMem O W).hom (g ^ n) • (show D.M W.1 from x₁) = (toMem O W).hom (g ^ n) • (show D.M W.1 from x₂)
    rw [hgn, ← sub_eq_zero, ← smul_sub, hn]

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"
end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

namespace GlueFromBasisSol
namespace GData

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}
variable (D : GData π B)

attribute [scoped instance] isLocalizedModule_resO

include D in
theorem exists_cover (U : V.affineOpens) :
    ∃ T : Finset Γ(V, U.1), Ideal.span (T : Set Γ(V, U.1)) = ⊤ ∧
      ∀ g ∈ T, (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B := by
  classical
  let s : Set Γ(V, U.1) := {g | (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B}
  have hs : Ideal.span s = ⊤ := by
    rw [← U.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => V.basicOpen_le _) ?_
    intro x hx
    obtain ⟨W, hWB, hxW⟩ := D.hcov x
    obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hx
    have hf : f ∈ s := D.hdown W ⟨V.basicOpen f, U.2.basicOpen f⟩ hfW hWB
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨T, hTs, hT⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hs)
  exact ⟨T, (Ideal.eq_top_iff_one _).mpr hT, fun g hg => hTs hg⟩

def cm (U : V.affineOpens) (g : Γ(V, U.1)) (hg : (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B) :
    Mem (B := B) U.1 :=
  ⟨⟨⟨V.basicOpen g, U.2.basicOpen g⟩, hg⟩, V.basicOpen_le g⟩

theorem cm_coe (U : V.affineOpens) (g : Γ(V, U.1)) (hg : (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B) :
    (cm U g hg).1.1.1 = V.basicOpen g := rfl

theorem boO_le_cm (U : V.affineOpens) (W : Mem (B := B) U.1) (g : Γ(V, U.1))
    (hg : (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B) :
    (D.boO U.1 W g).1.1.1 ≤ (cm U g hg).1.1.1 := by
  rw [D.boO_coe']; exact inf_le_right

theorem boO_mono (O : V.Opens) {W W' : Mem (B := B) O} (h : W'.1.1.1 ≤ W.1.1.1) (g : Γ(V, O)) :
    (D.boO O W' g).1.1.1 ≤ (D.boO O W g).1.1.1 := by
  rw [D.boO_coe', D.boO_coe']; exact inf_le_inf_right _ h

theorem MO_eq_zero_of_forall (O : V.Opens) (W : Mem (B := B) O) (s : Set Γ(V, O)) (hs : Ideal.span s = ⊤)
    (x : D.MO O W) (h : ∀ r ∈ s, D.resO O (D.boO_le O W r) x = 0) : x = 0 :=
  Module.eq_zero_of_isLocalized_span s hs (fun r : s => D.MO O (D.boO O W r.1))
    (fun r : s => D.resO O (D.boO_le O W r.1)) x (fun r => h r.1 r.2)

theorem MO_eq_of_forall (O : V.Opens) (W : Mem (B := B) O) (s : Set Γ(V, O)) (hs : Ideal.span s = ⊤)
    (x y : D.MO O W) (h : ∀ r ∈ s, D.resO O (D.boO_le O W r) x = D.resO O (D.boO_le O W r) y) : x = y := by
  rw [← sub_eq_zero]
  exact D.MO_eq_zero_of_forall O W s hs _ fun r hr => by rw [map_sub, sub_eq_zero]; exact h r hr

theorem G_eq_zero_of_forall_cm (U : V.affineOpens) (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (hB : ∀ g ∈ T, (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B)
    (t : D.G.obj U.1) (h : ∀ (g : Γ(V, U.1)) (hg : g ∈ T), t.1 (cm U g (hB g hg)) = 0) : t = 0 := by
  refine D.G_ext fun W => ?_
  show (show D.MO U.1 W from t.1 W) = 0
  refine D.MO_eq_zero_of_forall U.1 W T hT _ fun r hr => ?_
  show D.res (D.boO_le U.1 W r) (t.1 W) = 0
  rw [t.2 W (D.boO U.1 W r) (D.boO_le U.1 W r), ← t.2 (cm U r (hB r hr)) (D.boO U.1 W r) (D.boO_le_cm U W r (hB r hr)),
    h r hr, map_zero]

theorem G_eq_of_forall_cm (U : V.affineOpens) (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (hB : ∀ g ∈ T, (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B)
    (t t' : D.G.obj U.1) (h : ∀ (g : Γ(V, U.1)) (hg : g ∈ T), t.1 (cm U g (hB g hg)) = t'.1 (cm U g (hB g hg))) :
    t = t' := by
  rw [← sub_eq_zero]
  exact D.G_eq_zero_of_forall_cm U T hT hB _ fun g hg => by
    show t.1 (cm U g (hB g hg)) - t'.1 (cm U g (hB g hg)) = 0
    rw [h g hg, sub_self]

theorem MO_exists_of_compatible (U : V.affineOpens) (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (W : Mem (B := B) U.1)
    (z : ∀ g : ↥T, D.MO U.1 (D.boO U.1 W g.1))
    (hz : ∀ g g' : ↥T,
      D.resO U.1 (D.boO_le U.1 (D.boO U.1 W g.1) g'.1) (z g) =
        D.resO U.1 ((D.boO_mono U.1 (D.boO_le U.1 W g.1) g'.1)) (z g')) :
    ∃ y : D.MO U.1 W, ∀ g : ↥T, D.resO U.1 (D.boO_le U.1 W g.1) y = z g := by
  classical
  have hrange : Set.range (fun g : ↥T => (g.1 : Γ(V, U.1))) = (T : Set Γ(V, U.1)) := by
    ext a; constructor
    · rintro ⟨g, rfl⟩; exact g.2
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Ideal.span (Set.range (fun g : ↥T => (g.1 : Γ(V, U.1)))) = ⊤ := by rw [hrange]; exact hT
  exact IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top (fun g : ↥T => (g.1 : Γ(V, U.1))) hspan
    (fun g : ↥T => D.resO U.1 (D.boO_le U.1 W g.1))
    (N₂ := fun g g' : ↥T => D.MO U.1 (D.boO U.1 (D.boO U.1 W g.1) g'.1))
    (fun g g' : ↥T => D.resO U.1 (D.boO_le U.1 (D.boO U.1 W g.1) g'.1))
    (fun g g' : ↥T => D.resO U.1 (D.boO_mono U.1 (D.boO_le U.1 W g.1) g'.1))
    (fun g g' => by
      refine LinearMap.ext fun x => ?_
      show D.resO U.1 _ (D.resO U.1 _ x) = D.resO U.1 _ (D.resO U.1 _ x)
      rw [D.resO_resO, D.resO_resO])
    z hz

theorem G_exists_of_compatible (U : V.affineOpens) (T : Finset Γ(V, U.1)) (hT : Ideal.span (T : Set Γ(V, U.1)) = ⊤)
    (hB : ∀ g ∈ T, (⟨V.basicOpen g, U.2.basicOpen g⟩ : V.affineOpens) ∈ B)
    (x : ∀ g : ↥T, D.M (cm U g.1 (hB g.1 g.2)).1)
    (hx : ∀ g g' : ↥T,
      D.res (D.boO_le U.1 (cm U g.1 (hB g.1 g.2)) g'.1) (x g) =
        D.res (D.boO_le_cm U (cm U g.1 (hB g.1 g.2)) g'.1 (hB g'.1 g'.2)) (x g')) :
    ∃ t : D.G.obj U.1, ∀ g : ↥T, t.1 (cm U g.1 (hB g.1 g.2)) = x g := by
  classical

  have hloc : ∀ W : Mem (B := B) U.1, ∃ y : D.MO U.1 W, ∀ g : ↥T,
      D.resO U.1 (D.boO_le U.1 W g.1) y =
        (show D.MO U.1 (D.boO U.1 W g.1) from D.res (D.boO_le_cm U W g.1 (hB g.1 g.2)) (x g)) := by
    intro W
    refine D.MO_exists_of_compatible U T hT W _ fun g g' => ?_
    show D.res _ (D.res _ (x g)) = D.res _ (D.res _ (x g'))
    rw [D.res_res, D.res_res]
    have h1 : (D.boO U.1 (D.boO U.1 W g.1) g'.1).1.1.1 ≤ (D.boO U.1 (cm U g.1 (hB g.1 g.2)) g'.1).1.1.1 :=
      D.boO_mono U.1 (D.boO_le_cm U W g.1 (hB g.1 g.2)) g'.1
    rw [← D.res_res h1 (D.boO_le U.1 (cm U g.1 (hB g.1 g.2)) g'.1), hx g g', D.res_res]
  choose y hy using hloc
  refine ⟨⟨fun W => y W, fun W W' h => ?_⟩, fun g => ?_⟩
  ·
    refine D.MO_eq_of_forall U.1 W' T hT _ _ fun r hr => ?_
    show D.res _ (D.res h (y W)) = D.res _ (y W')
    have e1 := hy W ⟨r, hr⟩
    have e2 := hy W' ⟨r, hr⟩
    change D.res _ (y W) = D.res _ (x ⟨r, hr⟩) at e1
    change D.res _ (y W') = D.res _ (x ⟨r, hr⟩) at e2
    rw [D.res_res, e2, ← D.res_res (D.boO_mono U.1 h r) (D.boO_le U.1 W r), e1, D.res_res]
  ·
    refine D.MO_eq_of_forall U.1 (cm U g.1 (hB g.1 g.2)) T hT _ _ fun r hr => ?_
    have e1 := hy (cm U g.1 (hB g.1 g.2)) ⟨r, hr⟩
    change D.res _ (y _) = D.res _ (x ⟨r, hr⟩) at e1
    show D.res _ (y _) = D.res _ (x g)
    rw [e1]
    exact (hx g ⟨r, hr⟩).symm

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"
end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

namespace GlueFromBasisSol
namespace GData

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}
variable (D : GData π B)

def GO (O U' : V.Opens) (_h : U' ≤ O) : Type u := D.G.obj U'

scoped instance instACG_GO (O U' : V.Opens) (h : U' ≤ O) : AddCommGroup (D.GO O U' h) :=
  inferInstanceAs (AddCommGroup (D.G.obj U'))

scoped instance (priority := low) instModSelf_GO (O U' : V.Opens) (h : U' ≤ O) : Module Γ(V, U') (D.GO O U' h) :=
  inferInstanceAs (Module Γ(V, U') (D.G.obj U'))

scoped instance instMod_GO (O U' : V.Opens) (h : U' ≤ O) : Module Γ(V, O) (D.GO O U' h) :=
  Module.compHom (D.G.obj U') (V.presheaf.map (homOfLE h).op).hom

theorem GO_smul_coe (O U' : V.Opens) (h : U' ≤ O) (a : Γ(V, O)) (t : D.GO O U' h) (W : Mem (B := B) U') :
    (show D.G.obj U' from a • t).1 W = (toMem O ⟨W.1, W.2.trans h⟩).hom a • (show D.G.obj U' from t).1 W := by
  show (toMem U' W).hom ((V.presheaf.map (homOfLE h).op).hom a) • _ = _
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

scoped instance instTower_GO (O U' : V.Opens) (h : U' ≤ O) :
    letI : Algebra Γ(V, O) Γ(V, U') := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower Γ(V, O) Γ(V, U') (D.GO O U' h) :=
  letI : Algebra Γ(V, O) Γ(V, U') := (V.presheaf.map (homOfLE h).op).hom.toAlgebra
  ⟨fun a b t => by
    show ((V.presheaf.map (homOfLE h).op).hom a * b) • (show D.G.obj U' from t) =
      (V.presheaf.map (homOfLE h).op).hom a • (b • (show D.G.obj U' from t))
    rw [mul_smul]⟩

def GresO (O : V.Opens) {U₁ U₂ : V.Opens} (h₁ : U₁ ≤ O) (h₂ : U₂ ≤ O) (h : U₂ ≤ U₁) :
    D.GO O U₁ h₁ →ₗ[Γ(V, O)] D.GO O U₂ h₂ where
  toFun t := (show D.GO O U₂ h₂ from D.G.res h (show D.G.obj U₁ from t))
  map_add' _ _ := rfl
  map_smul' a t := D.G_ext fun W => by
    show ((toMem U₁ ⟨W.1, W.2.trans h⟩).hom ((V.presheaf.map (homOfLE h₁).op).hom a)) • _ =
      (toMem U₂ W).hom ((V.presheaf.map (homOfLE h₂).op).hom a) • _
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl

theorem GresO_coe (O : V.Opens) {U₁ U₂ : V.Opens} (h₁ : U₁ ≤ O) (h₂ : U₂ ≤ O) (h : U₂ ≤ U₁) (t : D.GO O U₁ h₁)
    (W : Mem (B := B) U₂) :
    (show D.G.obj U₂ from D.GresO O h₁ h₂ h t).1 W = (show D.G.obj U₁ from t).1 ⟨W.1, W.2.trans h⟩ := rfl

theorem G_eq_zero_of_forall_boO (O : V.Opens) (s : Set Γ(V, O)) (hs : Ideal.span s = ⊤) (t : D.G.obj O)
    (h : ∀ (W : Mem (B := B) O) (r : Γ(V, O)), r ∈ s → t.1 (D.boO O W r) = 0) : t = 0 := by
  refine D.G_ext fun W => ?_
  show (show D.MO O W from t.1 W) = 0
  refine D.MO_eq_zero_of_forall O W s hs _ fun r hr => ?_
  show D.res (D.boO_le O W r) (t.1 W) = 0
  rw [t.2 W (D.boO O W r) (D.boO_le O W r), h W r hr]

theorem isLocalizedModule_GresO (U : V.affineOpens) (f : Γ(V, U.1)) :
    IsLocalizedModule (Submonoid.powers f)
      (D.GresO U.1 le_rfl (V.basicOpen_le f) (V.basicOpen_le f)) := by
  classical
  obtain ⟨T, hT, hB⟩ := D.exists_cover U

  have hTf : Ideal.span (((fun r => (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom r) '' (T : Set Γ(V, U.1)))) = ⊤ := by
    rw [← Ideal.map_span, hT, Ideal.map_top]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n)) := by
      rw [map_pow]; exact (V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen f).pow n
    have hb : Function.Bijective (fun y : D.G.obj (V.basicOpen f) =>
        (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  ·
    intro y

    let Wg : ↥T → Mem (B := B) U.1 := fun g => cm U g.1 (hB g.1 g.2)
    let Bg : ↥T → Mem (B := B) U.1 := fun g => D.boO U.1 (Wg g) f
    have hBf : ∀ g : ↥T, (Bg g).1.1.1 ≤ V.basicOpen f := fun g => by
      show (D.boO U.1 (Wg g) f).1.1.1 ≤ _
      rw [D.boO_coe']; exact inf_le_right
    let yg : ∀ g : ↥T, D.MO U.1 (Bg g) := fun g => (show D.G.obj (V.basicOpen f) from y).1 ⟨(Bg g).1, hBf g⟩

    have h1 : ∀ g : ↥T, ∃ (n : ℕ) (x : D.MO U.1 (Wg g)), D.resO U.1 (D.boO_le U.1 (Wg g) f) x = f ^ n • yg g := by
      intro g
      obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := (D.isLocalizedModule_resO U.1 (Wg g) f).surj (yg g)
      exact ⟨n, x, hx.symm⟩
    choose n x hx using h1
    let N : ℕ := Finset.univ.sup n
    have hnN : ∀ g, n g ≤ N := fun g => Finset.le_sup (Finset.mem_univ g)
    obtain ⟨x', hx'⟩ : ∃ x' : ∀ g : ↥T, D.MO U.1 (Wg g), ∀ g, D.resO U.1 (D.boO_le U.1 (Wg g) f) (x' g) = f ^ N • yg g := by
      refine ⟨fun g => f ^ (N - n g) • x g, fun g => ?_⟩
      show D.resO U.1 _ (f ^ (N - n g) • x g) = _
      rw [map_smul, hx, smul_smul, ← pow_add, Nat.sub_add_cancel (hnN g)]

    have h2 : ∀ g g' : ↥T, ∃ m : ℕ, f ^ m • (D.resO U.1 (D.boO_le U.1 (Wg g) g'.1) (x' g) -
        D.resO U.1 (D.boO_le_cm U (Wg g) g'.1 (hB g'.1 g'.2)) (x' g')) = 0 := by
      intro g g'

      have hle1 : (D.boO U.1 (D.boO U.1 (Wg g) g'.1) f).1.1.1 ≤ (Bg g).1.1.1 := by
        show _ ≤ (D.boO U.1 (Wg g) f).1.1.1
        rw [D.boO_coe', D.boO_coe', D.boO_coe']; exact inf_le_inf_right _ inf_le_left
      have hle2 : (D.boO U.1 (D.boO U.1 (Wg g) g'.1) f).1.1.1 ≤ (Bg g').1.1.1 := by
        show _ ≤ (D.boO U.1 (Wg g') f).1.1.1
        rw [D.boO_coe', D.boO_coe', D.boO_coe']
        exact inf_le_inf_right _ inf_le_right
      have key : D.resO U.1 (D.boO_le U.1 (D.boO U.1 (Wg g) g'.1) f)
          (D.resO U.1 (D.boO_le U.1 (Wg g) g'.1) (x' g) -
            D.resO U.1 (D.boO_le_cm U (Wg g) g'.1 (hB g'.1 g'.2)) (x' g')) = 0 := by
        rw [map_sub, D.resO_resO, D.resO_resO, sub_eq_zero,
          ← D.resO_resO U.1 (D.boO_le U.1 (Wg g) f) hle1, hx',
          ← D.resO_resO U.1 (D.boO_le U.1 (Wg g') f) hle2, hx', map_smul, map_smul]
        congr 1
        show D.res hle1 ((show D.G.obj (V.basicOpen f) from y).1 ⟨(Bg g).1, hBf g⟩) =
          D.res hle2 ((show D.G.obj (V.basicOpen f) from y).1 ⟨(Bg g').1, hBf g'⟩)
        rw [(show D.G.obj (V.basicOpen f) from y).2 ⟨(Bg g).1, hBf g⟩ ⟨_, hle1.trans (hBf g)⟩ hle1,
          (show D.G.obj (V.basicOpen f) from y).2 ⟨(Bg g').1, hBf g'⟩ ⟨_, hle1.trans (hBf g)⟩ hle2]
      obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
        (D.isLocalizedModule_resO U.1 (D.boO U.1 (Wg g) g'.1) f).exists_of_eq (key.trans (map_zero _).symm)
      exact ⟨m, by simp only [smul_zero] at hm; exact hm⟩
    choose m hm using h2
    let M' : ℕ := Finset.univ.sup fun p : ↥T × ↥T => m p.1 p.2
    have hmM : ∀ g g', m g g' ≤ M' := fun g g' =>
      Finset.le_sup (f := fun p : ↥T × ↥T => m p.1 p.2) (Finset.mem_univ (g, g'))
    obtain ⟨x'', hx'', hcompat⟩ : ∃ x'' : ∀ g : ↥T, D.MO U.1 (Wg g),
        (∀ g, D.resO U.1 (D.boO_le U.1 (Wg g) f) (x'' g) = f ^ (M' + N) • yg g) ∧
        (∀ g g' : ↥T, D.resO U.1 (D.boO_le U.1 (Wg g) g'.1) (x'' g) =
          D.resO U.1 (D.boO_le_cm U (Wg g) g'.1 (hB g'.1 g'.2)) (x'' g')) := by
      refine ⟨fun g => f ^ M' • x' g, fun g => ?_, fun g g' => ?_⟩
      · show D.resO U.1 _ (f ^ M' • x' g) = _
        rw [map_smul, hx', smul_smul, ← pow_add]
      · show D.resO U.1 _ (f ^ M' • x' g) = D.resO U.1 _ (f ^ M' • x' g')
        rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub, ← Nat.sub_add_cancel (hmM g g'), pow_add, mul_smul, hm,
          smul_zero]
    obtain ⟨t, ht⟩ := D.G_exists_of_compatible U T hT hB (fun g => (show D.M (cm U g.1 (hB g.1 g.2)).1 from x'' g)) hcompat
    refine ⟨⟨(show D.GO U.1 U.1 le_rfl from t), ⟨f ^ (M' + N), M' + N, rfl⟩⟩, ?_⟩

    show f ^ (M' + N) • y = D.GresO U.1 le_rfl (V.basicOpen_le f) (V.basicOpen_le f) t
    rw [← sub_eq_zero]
    refine D.G_eq_zero_of_forall_boO (V.basicOpen f) _ hTf _ fun W r hr => ?_
    obtain ⟨g, hgT, rfl⟩ := hr

    set P : Mem (B := B) (V.basicOpen f) :=
      D.boO (V.basicOpen f) W ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom g) with hP
    have hWB : P.1.1.1 ≤ (Bg ⟨g, hgT⟩).1.1.1 := by
      show (D.boO (V.basicOpen f) W _).1.1.1 ≤ (D.boO U.1 (Wg ⟨g, hgT⟩) f).1.1.1
      rw [D.boO_coe', D.boO_coe', cm_coe, V.basicOpen_res]
      exact inf_le_right.trans (le_inf inf_le_right inf_le_left)
    let P' : Mem (B := B) U.1 := ⟨P.1, hWB.trans ((D.boO_le U.1 (Wg ⟨g, hgT⟩) f).trans (Wg ⟨g, hgT⟩).2)⟩
    show (show D.G.obj (V.basicOpen f) from f ^ (M' + N) • y).1 P -
        (show D.G.obj (V.basicOpen f) from D.GresO U.1 le_rfl (V.basicOpen_le f) (V.basicOpen_le f) t).1 P = 0
    rw [D.GO_smul_coe, D.GresO_coe, sub_eq_zero]
    have hyc := (show D.G.obj (V.basicOpen f) from y).2 ⟨(Bg ⟨g, hgT⟩).1, hBf ⟨g, hgT⟩⟩ P hWB
    have htc := t.2 (Wg ⟨g, hgT⟩) P' (hWB.trans (D.boO_le U.1 (Wg ⟨g, hgT⟩) f))
    have hx3 := hx'' ⟨g, hgT⟩
    change D.res _ (show D.M (Wg ⟨g, hgT⟩).1 from x'' ⟨g, hgT⟩) =
      (toMem U.1 (Bg ⟨g, hgT⟩)).hom (f ^ (M' + N)) • (show D.G.obj (V.basicOpen f) from y).1 ⟨(Bg ⟨g, hgT⟩).1, hBf _⟩ at hx3
    show (toMem U.1 ⟨P.1, P.2.trans (V.basicOpen_le f)⟩).hom (f ^ (M' + N)) • (show D.G.obj (V.basicOpen f) from y).1 P =
      t.1 ⟨P.1, _⟩
    rw [← hyc, show t.1 ⟨P.1, P.2.trans (V.basicOpen_le f)⟩ = t.1 P' from rfl, ← htc, ht ⟨g, hgT⟩,
      ← D.res_res hWB (D.boO_le U.1 (Wg ⟨g, hgT⟩) f)]
    change _ = D.res hWB (D.res _ (show D.M (Wg ⟨g, hgT⟩).1 from x'' ⟨g, hgT⟩))
    rw [hx3, D.res_smul, map_toMem U.1 (Bg ⟨g, hgT⟩) P' hWB]
  ·
    intro t₁ t₂ h12
    let Wg : ↥T → Mem (B := B) U.1 := fun g => cm U g.1 (hB g.1 g.2)
    have hBf : ∀ g : ↥T, (D.boO U.1 (Wg g) f).1.1.1 ≤ V.basicOpen f := fun g => by
      rw [D.boO_coe']; exact inf_le_right

    have h1 : ∀ g : ↥T, ∃ n : ℕ, f ^ n • ((show D.MO U.1 (Wg g) from (show D.G.obj U.1 from t₁).1 (Wg g)) -
        (show D.MO U.1 (Wg g) from (show D.G.obj U.1 from t₂).1 (Wg g))) = 0 := by
      intro g
      have key : D.resO U.1 (D.boO_le U.1 (Wg g) f)
          ((show D.MO U.1 (Wg g) from (show D.G.obj U.1 from t₁).1 (Wg g)) -
            (show D.MO U.1 (Wg g) from (show D.G.obj U.1 from t₂).1 (Wg g))) = 0 := by
        rw [map_sub, sub_eq_zero]
        show D.res _ ((show D.G.obj U.1 from t₁).1 (Wg g)) = D.res _ ((show D.G.obj U.1 from t₂).1 (Wg g))
        rw [(show D.G.obj U.1 from t₁).2 (Wg g) (D.boO U.1 (Wg g) f) (D.boO_le U.1 (Wg g) f),
          (show D.G.obj U.1 from t₂).2 (Wg g) (D.boO U.1 (Wg g) f) (D.boO_le U.1 (Wg g) f)]
        have := congrArg (fun s : D.GO U.1 (V.basicOpen f) (V.basicOpen_le f) =>
          (show D.G.obj (V.basicOpen f) from s).1 ⟨(D.boO U.1 (Wg g) f).1, hBf g⟩) h12
        exact this
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (D.isLocalizedModule_resO U.1 (Wg g) f).exists_of_eq (key.trans (map_zero _).symm)
      exact ⟨n, by simp only [smul_zero] at hn; exact hn⟩
    choose n hn using h1
    let N : ℕ := Finset.univ.sup n
    have hnN : ∀ g, n g ≤ N := fun g => Finset.le_sup (Finset.mem_univ g)
    refine ⟨⟨f ^ N, N, rfl⟩, ?_⟩
    show f ^ N • t₁ = f ^ N • t₂
    rw [← sub_eq_zero, ← smul_sub]
    refine D.G_eq_zero_of_forall_cm U T hT hB _ fun g hg => ?_
    show (toMem U.1 (Wg ⟨g, hg⟩)).hom ((V.presheaf.map (homOfLE (le_refl U.1)).op).hom (f ^ N)) •
      ((show D.G.obj U.1 from t₁).1 (Wg ⟨g, hg⟩) - (show D.G.obj U.1 from t₂).1 (Wg ⟨g, hg⟩)) = 0
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    change (f ^ N • ((show D.MO U.1 (Wg ⟨g, hg⟩) from (show D.G.obj U.1 from t₁).1 (Wg ⟨g, hg⟩)) -
        (show D.MO U.1 (Wg ⟨g, hg⟩) from (show D.G.obj U.1 from t₂).1 (Wg ⟨g, hg⟩))) : D.MO U.1 (Wg ⟨g, hg⟩)) = 0
    rw [← Nat.sub_add_cancel (hnN ⟨g, hg⟩), pow_add, mul_smul, hn, smul_zero]

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"
end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

namespace GlueFromBasisSol
namespace GData

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}
variable (D : GData π B)

attribute [scoped instance] isLocalizedModule_GresO

theorem GO_self_smul (O : V.Opens) (a : Γ(V, O)) (t : D.GO O O le_rfl) :
    a • t = (show D.GO O O le_rfl from a • (show D.G.obj O from t)) := by
  refine D.G_ext fun W => ?_
  rw [D.GO_smul_coe]
  rfl

theorem G_isQuasicoherent : D.G.IsQuasicoherent := by
  intro U f
  have hloc := D.isLocalizedModule_GresO U f
  refine ⟨fun y => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨t, ⟨_, n, rfl⟩⟩, h⟩ := hloc.surj (show D.GO U.1 (V.basicOpen f) (V.basicOpen_le f) from y)
    exact ⟨n, (show D.G.obj U.1 from t), h.symm⟩
  · have h0 : D.GresO U.1 le_rfl (V.basicOpen_le f) (V.basicOpen_le f) (show D.GO U.1 U.1 le_rfl from t) =
        D.GresO U.1 le_rfl (V.basicOpen_le f) (V.basicOpen_le f) 0 := by
      rw [map_zero]; exact ht
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hloc.exists_of_eq h0
    refine ⟨n, ?_⟩
    have hn' : (f ^ n • (show D.GO U.1 U.1 le_rfl from t) : D.GO U.1 U.1 le_rfl) = 0 := by
      simp only [smul_zero] at hn
      exact hn
    rw [D.GO_self_smul] at hn'
    exact hn'

theorem G_finite_mem (W : ↥B) : Module.Finite Γ(V, W.1.1) (D.G.obj W.1.1) := by
  haveI := D.hfg W
  let l : D.M W →ₗ[Γ(V, W.1.1)] D.G.obj W.1.1 :=
    { toFun := fun x => (D.e W).symm x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        apply (D.e W).injective
        rw [LinearEquiv.apply_symm_apply, D.e_smul, LinearEquiv.apply_symm_apply]
        rfl }
  exact Module.Finite.of_surjective l fun t => ⟨D.e W t, (D.e W).symm_apply_apply t⟩

theorem G_isCoherent : D.G.IsCoherent := by
  classical
  intro U
  obtain ⟨T, hT, hB⟩ := D.exists_cover U

  have key : Module.Finite Γ(V, U.1) (D.GO U.1 U.1 le_rfl) := by
    haveI : ∀ g : ↥T, IsLocalization.Away (g.1 : Γ(V, U.1)) Γ(V, V.basicOpen g.1) :=
      fun g => U.2.isLocalization_basicOpen g.1
    refine Module.Finite.of_localizationSpan_finite' T hT
      (Mₚ := fun g : ↥T => D.GO U.1 (V.basicOpen g.1) (V.basicOpen_le g.1))
      (Rₚ := fun g : ↥T => Γ(V, V.basicOpen g.1))
      (fun g : ↥T => D.GresO U.1 le_rfl (V.basicOpen_le g.1) (V.basicOpen_le g.1)) fun g => ?_
    exact D.G_finite_mem ⟨⟨V.basicOpen g.1, U.2.basicOpen g.1⟩, hB g.1 g.2⟩
  let l : D.GO U.1 U.1 le_rfl →ₗ[Γ(V, U.1)] D.G.obj U.1 :=
    { toFun := fun t => (show D.G.obj U.1 from t)
      map_add' := fun _ _ => rfl
      map_smul' := fun a t => D.GO_self_smul U.1 a t }
  exact Module.Finite.of_surjective l fun t => ⟨t, rfl⟩

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"
end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

namespace GlueFromBasisSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} {B : Set V.affineOpens}
variable (D : GData π B)

section FSide

variable (F : OModulePresheaf π)

theorem eq_of_forall_isLocalizedModule_eq {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
    {ι : Type*} [Fintype ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (f : ∀ i, M →ₗ[S] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    (x y : M) (h : ∀ i, f i x = f i y) : x = y := by
  classical
  have hex : ∀ i, ∃ n : ℕ, g i ^ n • x = g i ^ n • y := fun i => by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp (h i)
    exact ⟨n, hn⟩
  choose n hn using hex
  let N := Finset.univ.sup n
  have hN : ∀ i, g i ^ N • x = g i ^ N • y := fun i => by
    have hle : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm, mul_smul, mul_smul, hn i]
  have hspan : Ideal.span (Set.range fun i => g i ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg N
    rw [← Set.range_comp] at this
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan.symm ▸ Submodule.mem_top (x := (1 : S)))
  calc x = (1 : S) • x := (one_smul S x).symm
    _ = (∑ i, c i * g i ^ N) • x := by rw [hc]
    _ = ∑ i, c i • (g i ^ N • x) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = ∑ i, c i • (g i ^ N • y) := by simp_rw [hN]
    _ = (∑ i, c i * g i ^ N) • y := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = y := by rw [hc, one_smul]

def FO (O : V.Opens) (W : V.Opens) (h : W ≤ O) : Type u := F.obj W

scoped instance instACG_FO (O W : V.Opens) (h : W ≤ O) : AddCommGroup (FO F O W h) :=
  inferInstanceAs (AddCommGroup (F.obj W))

scoped instance instMod_FO (O W : V.Opens) (h : W ≤ O) : Module Γ(V, O) (FO F O W h) :=
  Module.compHom (F.obj W) (V.presheaf.map (homOfLE h).op).hom

theorem FO_smul_def (O W : V.Opens) (h : W ≤ O) (a : Γ(V, O)) (x : FO F O W h) :
    a • x = (show FO F O W h from (V.presheaf.map (homOfLE h).op).hom a • (show F.obj W from x)) := rfl

def FresO (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) :
    FO F O W hW →ₗ[Γ(V, O)] FO F O W' hW' where
  toFun x := (show FO F O W' hW' from F.res h (show F.obj W from x))
  map_add' x y := map_add (F.res h) _ _
  map_smul' a x := by
    show F.res h ((V.presheaf.map (homOfLE hW).op).hom a • (show F.obj W from x)) =
      (V.presheaf.map (homOfLE hW').op).hom a • F.res h _
    rw [F.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl

theorem FresO_apply (O : V.Opens) {W W' : V.Opens} (hW : W ≤ O) (hW' : W' ≤ O) (h : W' ≤ W) (x : FO F O W hW) :
    FresO F O hW hW' h x = (show FO F O W' hW' from F.res h (show F.obj W from x)) := rfl

def Fres₀ (O : V.Opens) {W : V.Opens} (hW : W ≤ O) : F.obj O →ₗ[Γ(V, O)] FO F O W hW where
  toFun x := (show FO F O W hW from F.res hW x)
  map_add' x y := map_add (F.res hW) _ _
  map_smul' a x := F.res_smul hW a x

theorem Fres₀_apply (O : V.Opens) {W : V.Opens} (hW : W ≤ O) (x : F.obj O) :
    Fres₀ F O hW x = (show FO F O W hW from F.res hW x) := rfl

variable {F}

theorem isLocalizedModule_FresO (hF : F.IsQuasicoherent) (O : V.Opens) (W : V.affineOpens) (hW : W.1 ≤ O)
    (g : Γ(V, O)) :
    IsLocalizedModule (Submonoid.powers g)
      (FresO F O hW ((V.basicOpen_le _).trans hW)
        (V.basicOpen_le ((V.presheaf.map (homOfLE hW).op).hom g))) := by
  set gW := (V.presheaf.map (homOfLE hW).op).hom g with hgW
  have hq := hF W gW
  have hres : ∀ n : ℕ, (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) =
      (V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom (gW ^ n) := fun n => by
    rw [hgW, ← map_pow, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le gW)).op).hom gW) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen gW
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n)) := by
      rw [hres, map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen gW) =>
        (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    refine ⟨((show FO F O W.1 hW from x), ⟨g ^ n, n, rfl⟩), ?_⟩
    show (V.presheaf.map (homOfLE ((V.basicOpen_le gW).trans hW)).op).hom (g ^ n) • (show F.obj _ from y) = F.res _ x
    rw [hres]; exact hx.symm
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le gW) ((show F.obj W.1 from x₁) - (show F.obj W.1 from x₂)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₁) =
      (V.presheaf.map (homOfLE hW).op).hom (g ^ n) • (show F.obj W.1 from x₂)
    rw [map_pow, ← hgW, ← sub_eq_zero, ← smul_sub, hn]

theorem isLocalizedModule_Fres₀ (hF : F.IsQuasicoherent) (U : V.affineOpens) (g : Γ(V, U.1)) :
    IsLocalizedModule (Submonoid.powers g) (Fres₀ F U.1 (V.basicOpen_le g)) := by
  have hq := hF U g
  have hunit : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom g) :=
    V.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
      rw [map_pow]; exact hunit.pow n
    have hb : Function.Bijective (fun y : F.obj (V.basicOpen g) =>
        (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n) • y) := hu.smul_bijective
    exact (Module.End.isUnit_iff _).mpr hb
  · intro y
    obtain ⟨n, x, hx⟩ := hq.1 y
    exact ⟨(x, ⟨g ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le g) (x₁ - x₂) = 0 := by rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hq.2 _ h0
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    show g ^ n • x₁ = g ^ n • x₂
    rw [← sub_eq_zero, ← smul_sub, hn]

theorem F_eq_of_forall_res_basicOpen_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type*} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤) (x y : F.obj U.1)
    (h : ∀ i, F.res (V.basicOpen_le (g i)) x = F.res (V.basicOpen_le (g i)) y) : x = y :=
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  eq_of_forall_isLocalizedModule_eq g hg (fun i => Fres₀ F U.1 (V.basicOpen_le (g i))) x y h

theorem F_exists_of_forall_res_eq (hF : F.IsQuasicoherent) (U : V.affineOpens)
    {ι : Type u} [Fintype ι] (g : ι → Γ(V, U.1)) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i, F.obj (V.basicOpen (g i)))
    (hx : ∀ i j, F.res (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))) (x i) =
      F.res (by rw [Scheme.basicOpen_res]; exact inf_le_right) (x j)) :
    ∃ m : F.obj U.1, ∀ i, F.res (V.basicOpen_le (g i)) m = x i := by
  haveI := fun i => isLocalizedModule_Fres₀ hF U (g i)
  let Ui : ι → V.affineOpens := fun i => ⟨V.basicOpen (g i), U.2.basicOpen (g i)⟩
  haveI := fun i j => isLocalizedModule_FresO hF U.1 (Ui i) (V.basicOpen_le (g i)) (g j)
  obtain ⟨m, hm⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hg
    (fun i => Fres₀ F U.1 (V.basicOpen_le (g i)))
    (fun i j => FresO F U.1 (V.basicOpen_le (g i)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (V.basicOpen_le ((V.presheaf.map (homOfLE (V.basicOpen_le (g i))).op).hom (g j))))
    (fun i j => FresO F U.1 (V.basicOpen_le (g j)) ((V.basicOpen_le _).trans (V.basicOpen_le (g i)))
      (by rw [Scheme.basicOpen_res]; exact inf_le_right))
    (fun i j => LinearMap.ext fun m => by
      show F.res _ (F.res _ m) = F.res _ (F.res _ m)
      rw [F.res_res, F.res_res])
    (fun i => (show FO F U.1 _ _ from x i)) (fun i j => hx i j)
  exact ⟨m, hm⟩

end FSide
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

namespace GData

section ClauseB

variable {F : OModulePresheaf π}

theorem affHom_ext {F₁ F₂ : OModulePresheaf π} (Φ Ψ : OModulePresheaf.AffHom F₁ F₂)
    (h : ∀ (U : V.affineOpens) (x : F₁.obj U.1), Φ.app U x = Ψ.app U x) : Φ = Ψ := by
  obtain ⟨a, _, _⟩ := Φ
  obtain ⟨b, _, _⟩ := Ψ
  have hab : a = b := funext fun U => LinearMap.ext (h U)
  subst hab
  rfl

theorem affHom_naturality_apply {F₁ F₂ : OModulePresheaf π} (Φ : OModulePresheaf.AffHom F₁ F₂)
    {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F₁.obj U'.1) :
    Φ.app U (F₁.res h x) = F₂.res h (Φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (Φ.naturality h)) x

variable (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] D.M W)
  (hϑs : ∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x)
  (hϑn : ∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = D.res h (ϑ W x))

def inApp (U : V.Opens) : F.obj U →ₗ[R] D.G.obj U where
  toFun y := ⟨fun W => ϑ W.1 (F.res W.2 y), fun W W' h => by
    rw [← hϑn W.1 W'.1 h, F.res_res]⟩
  map_add' y y' := D.G_ext fun W => by
    show ϑ W.1 (F.res W.2 (y + y')) = ϑ W.1 (F.res W.2 y) + ϑ W.1 (F.res W.2 y')
    rw [map_add, map_add]
  map_smul' r y := D.G_ext fun W => by
    show ϑ W.1 (F.res W.2 (r • y)) = r • ϑ W.1 (F.res W.2 y)
    rw [LinearMap.map_smul, LinearMap.map_smul]

theorem inApp_coe (U : V.Opens) (y : F.obj U) (W : Mem (B := B) U) :
    (D.inApp ϑ hϑn U y).1 W = ϑ W.1 (F.res W.2 y) := rfl

def inHom : OModulePresheaf.AffHom F D.G where
  app U := D.inApp ϑ hϑn U.1
  app_smul U a y := D.G_ext fun W => by
    rw [inApp_coe, G_smul_coe, inApp_coe, F.res_smul, hϑs]
  naturality {U U'} h := LinearMap.ext fun y => D.G_ext fun W => by
    show ϑ W.1 (F.res W.2 (F.res h y)) = (D.G.res h (D.inApp ϑ hϑn U'.1 y)).1 W
    rw [G_res_coe, inApp_coe, F.res_res]

theorem e_inHom_app (W : ↥B) (x : F.obj W.1.1) : D.e W ((D.inHom ϑ hϑs hϑn).app W.1 x) = ϑ W x := by
  show ϑ W (F.res (le_refl W.1.1) x) = ϑ W x
  rw [F.res_refl]; rfl

include hϑs hϑn in

theorem existsUnique_in :
    ∃! Ψ : OModulePresheaf.AffHom F D.G, ∀ (W : ↥B) (x : F.obj W.1.1), D.e W (Ψ.app W.1 x) = ϑ W x := by
  refine ⟨D.inHom ϑ hϑs hϑn, D.e_inHom_app ϑ hϑs hϑn, fun Ψ hΨ => ?_⟩
  refine affHom_ext _ _ fun U y => D.G_ext fun W => ?_
  rw [D.coe_eq_e_res (Ψ.app U y) W]
  show D.e W.1 (D.G.res W.2 (Ψ.app U y)) = ϑ W.1 (F.res W.2 y)
  rw [← affHom_naturality_apply Ψ (U := W.1.1) (U' := U) W.2 y, hΨ]

end ClauseB
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

section ClauseA

variable {F : OModulePresheaf π} (hF : F.IsQuasicoherent)
  (θ : ∀ W : ↥B, D.M W →ₗ[R] F.obj W.1.1)
  (hθs : ∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : D.M W), θ W (a • x) = a • θ W x)
  (hθn : ∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : D.M W), θ W' (D.res h x) = F.res h (θ W x))

def cov (U : V.affineOpens) : Finset Γ(V, U.1) := (D.exists_cover U).choose

theorem cov_span (U : V.affineOpens) : Ideal.span (Set.range fun g : ↥(D.cov U) => (g : Γ(V, U.1))) = ⊤ := by
  have h := (D.exists_cover U).choose_spec.1
  have hr : (Set.range fun g : ↥(D.cov U) => (g : Γ(V, U.1))) = ((D.cov U : Finset Γ(V, U.1)) : Set Γ(V, U.1)) := by
    ext x
    exact ⟨by rintro ⟨⟨y, hy⟩, rfl⟩; exact hy, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hr]; exact h

theorem cov_mem (U : V.affineOpens) (g : ↥(D.cov U)) :
    (⟨V.basicOpen (g : Γ(V, U.1)), U.2.basicOpen _⟩ : V.affineOpens) ∈ B :=
  (D.exists_cover U).choose_spec.2 g.1 g.2

def covMem (U : V.affineOpens) (g : ↥(D.cov U)) : Mem (B := B) U.1 :=
  ⟨⟨⟨V.basicOpen (g : Γ(V, U.1)), U.2.basicOpen _⟩, D.cov_mem U g⟩, V.basicOpen_le _⟩

include hθn in

theorem res_theta_eq (U : V.Opens) (t : D.G.obj U) (W : Mem (B := B) U) (a : Γ(V, W.1.1.1)) :
    F.res (V.basicOpen_le a) (θ W.1 (t.1 W)) = θ (D.bo W.1 a) (t.1 ⟨D.bo W.1 a, (D.bo_le W.1 a).trans W.2⟩) := by
  have h1 := hθn W.1 (D.bo W.1 a) (D.bo_le W.1 a) (t.1 W)
  have h2 := t.2 W ⟨D.bo W.1 a, (D.bo_le W.1 a).trans W.2⟩ (D.bo_le W.1 a)
  rw [h2] at h1
  exact h1.symm

include hF hθn in

theorem out_exists (U : V.affineOpens) (t : D.G.obj U.1) :
    ∃ m : F.obj U.1, ∀ W : Mem (B := B) U.1, F.res W.2 m = θ W.1 (t.1 W) := by
  classical

  obtain ⟨m, hm⟩ := F_exists_of_forall_res_eq hF U (fun g : ↥(D.cov U) => (g : Γ(V, U.1))) (D.cov_span U)
    (fun g => θ (D.covMem U g).1 (t.1 (D.covMem U g))) (fun i j => by

      have hle : (D.bo (D.covMem U i).1 ((V.presheaf.map (homOfLE (V.basicOpen_le (i : Γ(V, U.1)))).op).hom j)).1.1 ≤
          (D.covMem U j).1.1.1 := by
        show V.basicOpen _ ≤ V.basicOpen _
        exact (V.basicOpen_res _ (homOfLE _).op).trans_le inf_le_right
      have e1 := D.res_theta_eq θ hθn U.1 t (D.covMem U i)
        ((V.presheaf.map (homOfLE (V.basicOpen_le (i : Γ(V, U.1)))).op).hom j)
      have e2 := hθn (D.covMem U j).1 (D.bo (D.covMem U i).1 _) hle (t.1 (D.covMem U j))
      have e3 := t.2 (D.covMem U j) ⟨D.bo (D.covMem U i).1 _, (D.bo_le _ _).trans (D.covMem U i).2⟩ hle
      rw [e3] at e2
      exact e1.trans e2)
  refine ⟨m, fun W => ?_⟩

  refine F_eq_of_forall_res_basicOpen_eq hF W.1.1
    (fun g : ↥(D.cov U) => (V.presheaf.map (homOfLE W.2).op).hom (g : Γ(V, U.1))) ?_ _ _ fun g => ?_
  · have h := Ideal.map_span (V.presheaf.map (homOfLE W.2).op).hom (Set.range fun g : ↥(D.cov U) => (g : Γ(V, U.1)))
    rw [D.cov_span U, Ideal.map_top, ← Set.range_comp] at h
    exact h.symm
  · have hle : (D.bo W.1 ((V.presheaf.map (homOfLE W.2).op).hom (g : Γ(V, U.1)))).1.1 ≤ (D.covMem U g).1.1.1 := by
      show V.basicOpen _ ≤ V.basicOpen _
      exact (V.basicOpen_res _ (homOfLE _).op).trans_le inf_le_right
    have e1 := D.res_theta_eq θ hθn U.1 t W ((V.presheaf.map (homOfLE W.2).op).hom (g : Γ(V, U.1)))
    have e2 := hθn (D.covMem U g).1 (D.bo W.1 _) hle (t.1 (D.covMem U g))
    have e3 := t.2 (D.covMem U g) ⟨D.bo W.1 _, (D.bo_le _ _).trans W.2⟩ hle
    have e4 := hm g
    have e5 : F.res (V.basicOpen_le ((V.presheaf.map (homOfLE W.2).op).hom (g : Γ(V, U.1)))) (F.res W.2 m) =
        F.res hle (F.res (D.covMem U g).2 m) :=
      (F.res_res _ _ m).trans (F.res_res hle (D.covMem U g).2 m).symm
    rw [e3] at e2
    exact e5.trans ((congrArg (F.res hle) e4).trans (e2.symm.trans e1.symm))

include hF in

theorem out_unique (U : V.affineOpens) (t : D.G.obj U.1) (m m' : F.obj U.1)
    (hm : ∀ W : Mem (B := B) U.1, F.res W.2 m = θ W.1 (t.1 W))
    (hm' : ∀ W : Mem (B := B) U.1, F.res W.2 m' = θ W.1 (t.1 W)) : m = m' := by
  classical
  exact F_eq_of_forall_res_basicOpen_eq hF U (fun g : ↥(D.cov U) => (g : Γ(V, U.1))) (D.cov_span U) m m'
    fun g => (hm (D.covMem U g)).trans (hm' (D.covMem U g)).symm

def outFun (U : V.affineOpens) (t : D.G.obj U.1) : F.obj U.1 := (D.out_exists hF θ hθn U t).choose

theorem outFun_spec (U : V.affineOpens) (t : D.G.obj U.1) (W : Mem (B := B) U.1) :
    F.res W.2 (D.outFun hF θ hθn U t) = θ W.1 (t.1 W) := (D.out_exists hF θ hθn U t).choose_spec W

theorem outFun_eq (U : V.affineOpens) (t : D.G.obj U.1) (m : F.obj U.1)
    (hm : ∀ W : Mem (B := B) U.1, F.res W.2 m = θ W.1 (t.1 W)) : D.outFun hF θ hθn U t = m :=
  D.out_unique hF θ U t _ _ (D.outFun_spec hF θ hθn U t) hm

def outApp (U : V.affineOpens) : D.G.obj U.1 →ₗ[R] F.obj U.1 where
  toFun := D.outFun hF θ hθn U
  map_add' t t' := by
    refine D.outFun_eq hF θ hθn U (t + t') _ fun W => ?_
    rw [map_add, D.outFun_spec, D.outFun_spec, ← map_add]; rfl
  map_smul' r t := by
    refine D.outFun_eq hF θ hθn U (r • t) _ fun W => ?_
    rw [LinearMap.map_smul, D.outFun_spec, ← LinearMap.map_smul]; rfl

def outHom : OModulePresheaf.AffHom D.G F where
  app := D.outApp hF θ hθn
  app_smul U a t := by
    show D.outFun hF θ hθn U (a • t) = a • D.outFun hF θ hθn U t
    refine D.outFun_eq hF θ hθn U (a • t) _ fun W => ?_
    rw [F.res_smul, D.outFun_spec, ← hθs, G_smul_coe]
  naturality {U U'} h := LinearMap.ext fun t => by
    show D.outFun hF θ hθn U (D.G.res h t) = F.res h (D.outFun hF θ hθn U' t)
    refine D.outFun_eq hF θ hθn U _ _ fun W => ?_
    rw [F.res_res, G_res_coe]
    exact D.outFun_spec hF θ hθn U' t ⟨W.1, W.2.trans h⟩

theorem outHom_app_member (W : ↥B) (t : D.G.obj W.1.1) : (D.outHom hF θ hθs hθn).app W.1 t = θ W (D.e W t) := by
  show D.outFun hF θ hθn W.1 t = θ W (t.1 ⟨W, le_rfl⟩)
  have h := D.outFun_spec hF θ hθn W.1 t ⟨W, le_rfl⟩
  rw [F.res_refl] at h
  exact h

include hF hθs hθn in

theorem existsUnique_out :
    ∃! Φ : OModulePresheaf.AffHom D.G F, ∀ (W : ↥B) (x : D.G.obj W.1.1), Φ.app W.1 x = θ W (D.e W x) := by
  refine ⟨D.outHom hF θ hθs hθn, D.outHom_app_member hF θ hθs hθn, fun Φ hΦ => ?_⟩
  refine affHom_ext _ _ fun U t => ?_
  symm
  show D.outFun hF θ hθn U t = Φ.app U t
  refine D.outFun_eq hF θ hθn U t _ fun W => ?_
  rw [← affHom_naturality_apply Φ (U := W.1.1) (U' := U) W.2 t, hΦ, ← D.coe_eq_e_res]

end ClauseA
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

end GlueFromBasisSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis.GlueFromBasisSol.GData"

open GlueFromBasisSol in
theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))

    (B : Set V.affineOpens)
    (hdown : ∀ (W W' : V.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
    (hcov : ∀ x : V, ∃ W ∈ B, x ∈ W.1)

    (M : ↥B → Type u) [∀ W, AddCommGroup (M W)] [∀ W, Module R (M W)] [∀ W, Module Γ(V, W.1.1) (M W)]
    [∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1; IsScalarTower R Γ(V, W.1.1) (M W)]
    (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[R] M W'))
    (res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(V, W.1.1)) (x : M W),
      res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x)
    (res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
    (res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
      res (h.trans h') x = res h (res h' x))
    (hqc : ∀ (W Wg : ↥B) (g : Γ(V, W.1.1)) (hWg : Wg.1.1 = V.basicOpen g),
      (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
          res (hWg.trans_le (V.basicOpen_le g)) x =
            (V.presheaf.map (homOfLE (hWg.trans_le (V.basicOpen_le g))).op).hom (g ^ n) • y) ∧
      (∀ x : M W, res (hWg.trans_le (V.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ W : ↥B, Module.Finite (Γ(V, W.1.1) : Type u) (M W)) :
    ∃ (G : OModulePresheaf π) (e : ∀ W : ↥B, G.obj W.1.1 ≃ₗ[R] M W),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : G.obj W.1.1), e W (a • x) = a • e W x) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : G.obj W.1.1), e W' (G.res h x) = res h (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (θ : ∀ W : ↥B, M W →ₗ[R] F.obj W.1.1),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : M W), θ W (a • x) = a • θ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θ W' (res h x) = F.res h (θ W x)) →
          ∃! Φ : OModulePresheaf.AffHom G F, ∀ (W : ↥B) (x : G.obj W.1.1), Φ.app W.1 x = θ W (e W x)) ∧

      (∀ (F : OModulePresheaf π), F.IsQuasicoherent →
        ∀ (ϑ : ∀ W : ↥B, F.obj W.1.1 →ₗ[R] M W),
          (∀ (W : ↥B) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), ϑ W (a • x) = a • ϑ W x) →
          (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : F.obj W.1.1), ϑ W' (F.res h x) = res h (ϑ W x)) →
          ∃! Ψ : OModulePresheaf.AffHom F G, ∀ (W : ↥B) (x : F.obj W.1.1), e W (Ψ.app W.1 x) = ϑ W x) := by
  let D : GlueFromBasisSol.GData π B :=
    { hdown := hdown, hcov := hcov, M := M, res := res, res_smul := res_smul, res_refl := res_refl,
      res_comp := res_comp, hqc := hqc, hfg := hfg }
  exact ⟨D.G, D.e, D.G_isCoherent, D.G_isQuasicoherent, D.e_smul, D.e_res,
    fun F hF θ hs hn => D.existsUnique_out hF θ hs hn, fun F _ ϑ hs hn => D.existsUnique_in ϑ hs hn⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis (solution)
