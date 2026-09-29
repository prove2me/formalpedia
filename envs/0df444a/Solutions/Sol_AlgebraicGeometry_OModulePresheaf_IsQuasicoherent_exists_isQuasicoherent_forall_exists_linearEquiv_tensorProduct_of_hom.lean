-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a5515f7a-8d8d-5326-a747-dff154e3bad3

import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Mathlib
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
import Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open CategoryTheory AlgebraicGeometry

universe u

namespace P1Sol

noncomputable section

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

abbrev rV {W₁ W₂ : V'.Opens} (h : W₁ ≤ W₂) : Γ(V', W₂) →+* Γ(V', W₁) := (V'.presheaf.map (homOfLE h).op).hom

abbrev rP {U₁ U₂ : P.Opens} (h : U₁ ≤ U₂) : Γ(P, U₂) →+* Γ(P, U₁) := (P.presheaf.map (homOfLE h).op).hom

theorem rV_refl {W : V'.Opens} (h : W ≤ W) (a : Γ(V', W)) : rV h a = a := by
  have : (homOfLE h).op = 𝟙 (op W) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  simp only [rV, this, CategoryTheory.Functor.map_id]; rfl

theorem rV_rV {W₁ W₂ W₃ : V'.Opens} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (a : Γ(V', W₃)) :
    rV h₁ (rV h₂ a) = rV (h₁.trans h₂) a := by
  show ((V'.presheaf.map (homOfLE h₂).op) ≫ V'.presheaf.map (homOfLE h₁).op).hom a = _
  rw [← Functor.map_comp]; rfl

theorem rP_rP {U₁ U₂ U₃ : P.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (a : Γ(P, U₃)) :
    rP h₁ (rP h₂ a) = rP (h₁.trans h₂) a := by
  show ((P.presheaf.map (homOfLE h₂).op) ≫ P.presheaf.map (homOfLE h₁).op).hom a = _
  rw [← Functor.map_comp]; rfl

structure Chart (p : V' ⟶ P) where
  U : P.affineOpens
  V : V'.affineOpens
  le : V.1 ≤ p ⁻¹ᵁ U.1

namespace Chart
variable {p : V' ⟶ P}

scoped instance : LE (Chart p) := ⟨fun c₁ c₂ => c₁.U.1 ≤ c₂.U.1 ∧ c₁.V.1 ≤ c₂.V.1⟩

theorem le_def (c₁ c₂ : Chart p) : c₁ ≤ c₂ ↔ c₁.U.1 ≤ c₂.U.1 ∧ c₁.V.1 ≤ c₂.V.1 := Iff.rfl
theorem le_rfl (c : Chart p) : c ≤ c := ⟨le_refl _, le_refl _⟩
theorem le_trans' {c₁ c₂ c₃ : Chart p} (h : c₁ ≤ c₂) (h' : c₂ ≤ c₃) : c₁ ≤ c₃ := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

abbrev φ (c : Chart p) : Γ(P, c.U.1) →+* Γ(V', c.V.1) := (p.appLE c.U.1 c.V.1 c.le).hom

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart"

scoped instance chartAlgebra (p : V' ⟶ P) (c : Chart p) : Algebra Γ(P, c.U.1) Γ(V', c.V.1) := c.φ.toAlgebra

theorem chart_algebraMap (p : V' ⟶ P) (c : Chart p) (a : Γ(P, c.U.1)) :
    algebraMap Γ(P, c.U.1) Γ(V', c.V.1) a = c.φ a := rfl

theorem rV_φ {p : V' ⟶ P} {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) (a : Γ(P, c₂.U.1)) :
    rV h.2 (c₂.φ a) = c₁.φ (rP h.1 a) := by
  show (p.appLE c₂.U.1 c₂.V.1 c₂.le ≫ V'.presheaf.map (homOfLE h.2).op).hom a =
    (P.presheaf.map (homOfLE h.1).op ≫ p.appLE c₁.U.1 c₁.V.1 c₁.le).hom a
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

abbrev Chart.RU {p : V' ⟶ P} (c : Chart p) : Type u := ↑(P.presheaf.obj (op c.U.1))

variable (p : V' ⟶ P) (G : OModulePresheaf q)

abbrev T (c : Chart p) : Type u := Γ(V', c.V.1) ⊗[c.RU] G.obj c.U.1

variable {p G}

noncomputable def tmap {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) : T p G c₂ →+ T p G c₁ :=
  TensorProduct.liftAddHom (R := c₂.RU)
    { toFun := fun b =>
        { toFun := fun x => rV h.2 b ⊗ₜ[c₁.RU] G.res h.1 x
          map_zero' := by simp
          map_add' := fun x y => by simp [TensorProduct.tmul_add] }
      map_zero' := by ext x; simp
      map_add' := fun b b' => by ext x; simp [TensorProduct.add_tmul] }
    (fun a b x => by
      show rV h.2 (a • b) ⊗ₜ[c₁.RU] G.res h.1 x = rV h.2 b ⊗ₜ[c₁.RU] G.res h.1 (a • x)
      rw [G.res_smul, Algebra.smul_def, map_mul, chart_algebraMap, rV_φ h, ← TensorProduct.smul_tmul,
        Algebra.smul_def, chart_algebraMap])

theorem tmap_tmul {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) (b : Γ(V', c₂.V.1)) (x : G.obj c₂.U.1) :
    tmap (G := G) h (b ⊗ₜ x) = rV h.2 b ⊗ₜ G.res h.1 x := rfl

theorem tmap_refl (c : Chart p) (t : T p G c) : tmap (G := G) c.le_rfl t = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [tmap_tmul, rV_refl, G.res_refl_apply]
  | add s t hs ht => rw [map_add, hs, ht]

theorem tmap_tmap {c₁ c₂ c₃ : Chart p} (h : c₁ ≤ c₂) (h' : c₂ ≤ c₃) (t : T p G c₃) :
    tmap (G := G) h (tmap h' t) = tmap (Chart.le_trans' h h') t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [tmap_tmul, tmap_tmul, tmap_tmul, rV_rV, G.res_res]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]

theorem tmap_smul {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) (a : Γ(V', c₂.V.1)) (t : T p G c₂) :
    tmap (G := G) h (a • t) = rV h.2 a • tmap h t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [TensorProduct.smul_tmul', tmap_tmul, tmap_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      smul_eq_mul, map_mul]
  | add s t hs ht => rw [smul_add, map_add, hs, ht, map_add, smul_add]

abbrev ChartIn (p : V' ⟶ P) (W : V'.Opens) : Type u := {c : Chart p // c.V.1 ≤ W}

def Fam (p : V' ⟶ P) (G : OModulePresheaf q) (W : V'.Opens) : Type u := ∀ c : ChartIn p W, T p G c.1

scoped instance (W : V'.Opens) : AddCommGroup (Fam p G W) := by unfold Fam; infer_instance

theorem Fam.add_apply {W : V'.Opens} (s t : Fam p G W) (c : ChartIn p W) : (s + t) c = s c + t c := rfl
theorem Fam.zero_apply {W : V'.Opens} (c : ChartIn p W) : (0 : Fam p G W) c = 0 := rfl
theorem Fam.neg_apply {W : V'.Opens} (s : Fam p G W) (c : ChartIn p W) : (-s) c = -(s c) := rfl
theorem Fam.sub_apply {W : V'.Opens} (s t : Fam p G W) (c : ChartIn p W) : (s - t) c = s c - t c := rfl

scoped instance Fam.instSMul (W : V'.Opens) : SMul Γ(V', W) (Fam p G W) :=
  ⟨fun a s c => rV c.2 a • s c⟩

p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam"
theorem Fam.smul_apply {W : V'.Opens} (a : Γ(V', W)) (s : Fam p G W) (c : ChartIn p W) :
    (a • s) c = rV c.2 a • s c := rfl

scoped instance Fam.instModule (W : V'.Opens) : Module Γ(V', W) (Fam p G W) where
  one_smul s := by funext c; rw [Fam.smul_apply, map_one, one_smul]
  mul_smul a b s := by funext c; simp only [Fam.smul_apply, map_mul, mul_smul]
  smul_zero a := by funext c; rw [Fam.smul_apply, Fam.zero_apply, smul_zero]
  smul_add a s t := by funext c; simp only [Fam.smul_apply, Fam.add_apply, smul_add]
  add_smul a b s := by funext c; simp only [Fam.smul_apply, Fam.add_apply, map_add, add_smul]
  zero_smul s := by funext c; rw [Fam.smul_apply, map_zero, zero_smul, Fam.zero_apply]

p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam"

def Sec (p : V' ⟶ P) (G : OModulePresheaf q) (W : V'.Opens) : Submodule Γ(V', W) (Fam p G W) where
  carrier := {s | ∀ (c₁ c₂ : ChartIn p W) (hle : c₁.1 ≤ c₂.1), tmap hle (s c₂) = s c₁}
  add_mem' {s t} hs ht := fun c₁ c₂ hle => by
    rw [Fam.add_apply, Fam.add_apply, map_add, hs c₁ c₂ hle, ht c₁ c₂ hle]
  zero_mem' := fun c₁ c₂ hle => by rw [Fam.zero_apply, Fam.zero_apply, map_zero]
  smul_mem' a {s} hs := fun c₁ c₂ hle => by
    rw [Fam.smul_apply, Fam.smul_apply, tmap_smul, hs c₁ c₂ hle, rV_rV]

theorem Sec.compat {W : V'.Opens} (s : Sec p G W) (c₁ c₂ : ChartIn p W) (hle : c₁.1 ≤ c₂.1) :
    tmap hle (s.1 c₂) = s.1 c₁ := s.2 c₁ c₂ hle

abbrev sc (p : V' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)) (W : V'.Opens) (r : A) : Γ(V', W) :=
  ((p ≫ q).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r)

theorem rV_sc {W₁ W₂ : V'.Opens} (h : W₁ ≤ W₂) (r : A) : rV h (sc p q W₂ r) = sc p q W₁ r := by
  show ((p ≫ q).appLE ⊤ W₂ le_top ≫ V'.presheaf.map (homOfLE h).op).hom _ = _
  rw [Scheme.Hom.appLE_map]

theorem algebraMap_eq_sc (W : V'.Opens) (r : A) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W).algebraMap r = sc p q W r := rfl

@[reducible] def Sec.moduleA (W : V'.Opens) : Module A (Sec p G W) :=
  Module.compHom (Sec p G W) (Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W).algebraMap

def resSec {W₁ W₂ : V'.Opens} (h : W₁ ≤ W₂) (s : Sec p G W₂) : Sec p G W₁ :=
  ⟨fun c => s.1 ⟨c.1, c.2.trans h⟩, fun c₁ c₂ hle => s.2 ⟨c₁.1, c₁.2.trans h⟩ ⟨c₂.1, c₂.2.trans h⟩ hle⟩

theorem resSec_apply {W₁ W₂ : V'.Opens} (h : W₁ ≤ W₂) (s : Sec p G W₂) (c : ChartIn p W₁) :
    (resSec h s).1 c = s.1 ⟨c.1, c.2.trans h⟩ := rfl

theorem Sec.ext' {W : V'.Opens} {s t : Sec p G W} (h : ∀ c : ChartIn p W, s.1 c = t.1 c) : s = t :=
  Subtype.ext (funext h)

theorem Sec.smul_apply {W : V'.Opens} (a : Γ(V', W)) (s : Sec p G W) (c : ChartIn p W) :
    (a • s).1 c = rV c.2 a • s.1 c := rfl

theorem Sec.smulA_apply {W : V'.Opens} (r : A) (s : Sec p G W) (c : ChartIn p W) :
    letI := Sec.moduleA (p := p) (G := G) W
    (r • s).1 c = sc p q c.1.V.1 r • s.1 c := by
  show rV c.2 (sc p q W r) • s.1 c = _
  rw [rV_sc]

variable (p G) in

def pullbackDatum : OModulePresheaf (p ≫ q) where
  obj W := Sec p G W
  addCommGroup W := inferInstance
  module W := Sec.moduleA W
  moduleSections W := inferInstance
  isScalarTower W := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p ≫ q) W
    letI := Sec.moduleA (p := p) (G := G) W
    exact ⟨fun r a s => by
      show ((algebraMap A Γ(V', W) r) * a) • s = (algebraMap A Γ(V', W) r) • (a • s)
      rw [mul_smul]⟩
  res {W₁ W₂} h :=
    letI := Sec.moduleA (p := p) (G := G) W₁
    letI := Sec.moduleA (p := p) (G := G) W₂
    { toFun := resSec h
      map_add' := fun s t => rfl
      map_smul' := fun r s => by
        apply Sec.ext'
        intro c
        rw [resSec_apply, Sec.smulA_apply, RingHom.id_apply, Sec.smulA_apply, resSec_apply] }
  res_smul {W₁ W₂} h a s := by
    apply Sec.ext'
    intro c
    show rV (c.2.trans h) a • s.1 ⟨c.1, c.2.trans h⟩ = rV c.2 (rV h a) • s.1 ⟨c.1, c.2.trans h⟩
    rw [rV_rV]
  res_refl W := by
    letI := Sec.moduleA (p := p) (G := G) W
    exact LinearMap.ext fun s => rfl
  res_comp {W₁ W₂ W₃} h h' := by
    letI := Sec.moduleA (p := p) (G := G) W₁
    letI := Sec.moduleA (p := p) (G := G) W₃
    exact LinearMap.ext fun s => rfl

theorem pullbackDatum_obj (W : V'.Opens) : (pullbackDatum p G).obj W = ↥(Sec p G W) := rfl

theorem pullbackDatum_res_apply {W₁ W₂ : V'.Opens} (h : W₁ ≤ W₂) (s : Sec p G W₂) (c : ChartIn p W₁) :
    ((pullbackDatum p G).res h s).1 c = s.1 ⟨c.1, c.2.trans h⟩ := rfl

def evₗ (c : Chart p) : Sec p G c.V.1 →ₗ[Γ(V', c.V.1)] T p G c where
  toFun s := s.1 ⟨c, le_rfl⟩
  map_add' s t := rfl
  map_smul' a s := by
    show rV (le_refl _) a • s.1 ⟨c, le_rfl⟩ = a • s.1 ⟨c, le_rfl⟩
    rw [rV_refl]

theorem evₗ_apply (c : Chart p) (s : Sec p G c.V.1) : evₗ (p := p) (G := G) c s = s.1 ⟨c, le_rfl⟩ := rfl

theorem evₗ_res {c₁ c₂ : Chart p} (hle : c₁ ≤ c₂) (s : Sec p G c₂.V.1) :
    evₗ c₁ ((pullbackDatum p G).res hle.2 s) = tmap hle (evₗ c₂ s) :=
  (s.2 ⟨c₁, hle.2⟩ ⟨c₂, le_rfl⟩ hle).symm

def tmapₗ {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) :
    letI : Module Γ(V', c₂.V.1) (T p G c₁) := Module.compHom (T p G c₁) (rV h.2)
    T p G c₂ →ₗ[Γ(V', c₂.V.1)] T p G c₁ :=
  letI : Module Γ(V', c₂.V.1) (T p G c₁) := Module.compHom (T p G c₁) (rV h.2)
  { toFun := tmap h, map_add' := map_add _, map_smul' := fun a t => tmap_smul h a t }

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam"

end P1Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

namespace P1Sol

noncomputable section

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
variable {p : V' ⟶ P} {G : OModulePresheaf q}

section L0

abbrev shrink (c : Chart p) (U' : P.affineOpens) (h' : c.V.1 ≤ p ⁻¹ᵁ U'.1) : Chart p := ⟨U', c.V, h'⟩

theorem shrink_le (c : Chart p) (U' : P.affineOpens) (hU : U'.1 ≤ c.U.1) (h' : c.V.1 ≤ p ⁻¹ᵁ U'.1) :
    shrink c U' h' ≤ c := ⟨hU, le_rfl⟩

theorem tmap_shrink_bijective (hq : G.IsQuasicoherent) (c : Chart p) (U' : P.affineOpens) (hU : U'.1 ≤ c.U.1)
    (h' : c.V.1 ≤ p ⁻¹ᵁ U'.1) :
    Function.Bijective (tmap (G := G) (shrink_le c U' hU h')) := by

  let c' : Chart p := shrink c U' h'
  letI iA : Algebra c.RU c'.RU := (rP hU).toAlgebra
  letI iV' : Algebra c'.RU Γ(V', c.V.1) := chartAlgebra p c'
  haveI iT : IsScalarTower c.RU c'.RU Γ(V', c.V.1) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      show c.φ a = c'.φ (rP hU a)
      rw [← rV_φ (shrink_le c U' hU h') a, rV_refl])
  obtain ⟨β, hβ⟩ :=
    OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res G hq c.U U' hU

  let inv : T p G c' → T p G c := fun t =>
    TensorProduct.AlgebraTensorModule.cancelBaseChange c.RU c'.RU c'.RU Γ(V', c.V.1) (G.obj c.U.1)
      (LinearMap.lTensor Γ(V', c.V.1) β.symm.toLinearMap t)
  have key : ∀ (b : Γ(V', c.V.1)) (z : c'.RU ⊗[c.RU] G.obj c.U.1),
      tmap (G := G) (shrink_le c U' hU h')
        (TensorProduct.AlgebraTensorModule.cancelBaseChange c.RU c'.RU c'.RU Γ(V', c.V.1) (G.obj c.U.1) (b ⊗ₜ z)) =
      b ⊗ₜ[c'.RU] β z := by
    intro b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, tmap_tmul, rV_refl,
        show a ⊗ₜ[c.RU] x = a • ((1 : c'.RU) ⊗ₜ[c.RU] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, hβ, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add z w hz hw => rw [TensorProduct.tmul_add, map_add, map_add, hz, hw, map_add, TensorProduct.tmul_add]
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, fun t => ?_, fun t => ?_⟩
  ·
    induction t using TensorProduct.induction_on with
    | zero => simp [inv]
    | tmul b x =>
      simp only [inv]
      rw [tmap_tmul, rV_refl, LinearMap.lTensor_tmul, LinearEquiv.coe_toLinearMap,
        show β.symm (G.res hU x) = (1 : c'.RU) ⊗ₜ[c.RU] x by rw [← hβ, LinearEquiv.symm_apply_apply],
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    | add s t hs ht => simp only [inv, map_add] at hs ht ⊢; rw [hs, ht]
  ·
    induction t using TensorProduct.induction_on with
    | zero => simp [inv]
    | tmul b y =>
      simp only [inv]
      rw [LinearMap.lTensor_tmul, LinearEquiv.coe_toLinearMap, key, LinearEquiv.apply_symm_apply]
    | add s t hs ht => simp only [inv, map_add] at hs ht ⊢; rw [hs, ht]

end L0
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

section L1

theorem rP_refl {U : P.Opens} (h : U ≤ U) (a : Γ(P, U)) : rP h a = a := by
  have : (homOfLE h).op = 𝟙 (op U) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  simp only [rP, this, CategoryTheory.Functor.map_id]; rfl

theorem tmapₗ_isLocalizedModule' (hq : G.IsQuasicoherent) {c₁ c₂ : Chart p} (h : c₁ ≤ c₂)
    (g : Γ(V', c₂.V.1)) (hV : c₁.V.1 = V'.basicOpen g) :
    letI : Module Γ(V', c₂.V.1) (T p G c₁) := Module.compHom (T p G c₁) (rV h.2)
    IsLocalizedModule (Submonoid.powers g) (tmapₗ (p := p) (G := G) h) := by

  letI algSL : Algebra Γ(V', c₂.V.1) Γ(V', c₁.V.1) := (rV h.2).toAlgebra
  haveI : IsLocalization.Away g Γ(V', c₁.V.1) := c₂.V.2.isLocalization_of_eq_basicOpen g (homOfLE h.2) hV

  let m : Chart p := ⟨c₂.U, c₁.V, h.2.trans c₂.le⟩
  have hm : m ≤ c₂ := ⟨le_rfl, h.2⟩
  letI algL : Algebra c₂.RU Γ(V', c₁.V.1) := chartAlgebra p m
  haveI towL : IsScalarTower c₂.RU Γ(V', c₂.V.1) Γ(V', c₁.V.1) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      show m.φ a = rV h.2 (c₂.φ a)
      rw [rV_φ hm a, rP_refl])
  letI instS₁ : Module Γ(V', c₂.V.1) (T p G c₁) := Module.compHom (T p G c₁) (rV h.2)

  let f₀ : T p G c₂ →ₗ[Γ(V', c₂.V.1)] Γ(V', c₁.V.1) ⊗[Γ(V', c₂.V.1)] T p G c₂ :=
    TensorProduct.mk Γ(V', c₂.V.1) Γ(V', c₁.V.1) (T p G c₂) 1
  haveI hf₀ : IsLocalizedModule (Submonoid.powers g) f₀ :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Γ(V', c₁.V.1) f₀).mpr
      (TensorProduct.isBaseChange Γ(V', c₂.V.1) (T p G c₂) Γ(V', c₁.V.1))

  let can := TensorProduct.AlgebraTensorModule.cancelBaseChange c₂.RU Γ(V', c₂.V.1) Γ(V', c₁.V.1)
    Γ(V', c₁.V.1) (G.obj c₂.U.1)
  have hbij := tmap_shrink_bijective hq m c₁.U h.1 c₁.le
  let sh : T p G m ≃ T p G c₁ := Equiv.ofBijective _ hbij
  have sh_apply : ∀ w, sh w = tmap (G := G) (shrink_le m c₁.U h.1 c₁.le) w := fun w => rfl
  let e : (Γ(V', c₁.V.1) ⊗[Γ(V', c₂.V.1)] T p G c₂) ≃ₗ[Γ(V', c₂.V.1)] T p G c₁ :=
    { toFun := fun z => sh (can z)
      invFun := fun t => can.symm (sh.symm t)
      map_add' := fun z w => by rw [map_add, sh_apply, sh_apply, sh_apply, map_add]
      map_smul' := fun s z => by
        rw [algebra_compatible_smul Γ(V', c₁.V.1) s z, map_smul, sh_apply, sh_apply, tmap_smul, rV_refl]
        rfl
      left_inv := fun z => by simp
      right_inv := fun t => by simp }
  have he : (e.toLinearMap ∘ₗ f₀) = tmapₗ (p := p) (G := G) h := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      show sh (can ((1 : Γ(V', c₁.V.1)) ⊗ₜ (b ⊗ₜ y))) = tmap h (b ⊗ₜ y)
      rw [sh_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one,
        tmap_tmul, tmap_tmul, rV_refl, RingHom.algebraMap_toAlgebra]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers g) f₀ e

end L1
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

section Alg

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem eq_of_forall_apply_eq {ι : Type*} [Fintype ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    {x y : M} (h : ∀ i, f i x = f i y) : x = y := by
  classical
  have hz : ∀ i, ∃ n : ℕ, g i ^ n • (x - y) = 0 := fun i => by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp
      (show f i (x - y) = f i 0 by rw [map_zero, map_sub, h i, sub_self])
    refine ⟨n, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero] at hn
    exact hn
  choose n hn using hz
  have hN : ∀ i, g i ^ (Finset.univ.sup n) • (x - y) = 0 := fun i => by
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i)), pow_add, mul_smul, hn, smul_zero]
  have hspan : Ideal.span (Set.range fun i => g i ^ (Finset.univ.sup n)) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg (Finset.univ.sup n)
    rwa [← Set.range_comp] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Submodule.mem_top : (1 : R) ∈ _)
  rw [← sub_eq_zero]
  calc x - y = (1 : R) • (x - y) := (one_smul _ _).symm
    _ = (∑ i, c i * g i ^ (Finset.univ.sup n)) • (x - y) := by rw [hc]
    _ = ∑ i, c i • (g i ^ (Finset.univ.sup n) • (x - y)) := by rw [Finset.sum_smul]; simp_rw [mul_smul]
    _ = 0 := by simp [hN]

theorem isLocalizedModule_of_smul_eq {S : Type*} [CommRing S] {M₁ N₁ : Type*} [AddCommGroup M₁] [AddCommGroup N₁]
    [Module R M₁] [Module R N₁] [Module S M₁] [Module S N₁] (f : M₁ →ₗ[R] N₁) (f' : M₁ →ₗ[S] N₁)
    (hff : ∀ m, f m = f' m) (r : R) (s : S) (hM : ∀ m : M₁, r • m = s • m) (hN : ∀ n : N₁, r • n = s • n)
    [IsLocalizedModule (Submonoid.powers s) f'] : IsLocalizedModule (Submonoid.powers r) f := by
  have hMn : ∀ (n : ℕ) (m : M₁), r ^ n • m = s ^ n • m := fun n => by
    induction n with
    | zero => intro m; simp
    | succ n ih => intro m; rw [pow_succ, mul_smul, hM, ih, ← mul_smul, ← pow_succ]
  have hNn : ∀ (n : ℕ) (x : N₁), r ^ n • x = s ^ n • x := fun n => by
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, mul_smul, hN, ih, ← mul_smul, ← pow_succ]
  constructor
  · rintro ⟨_, n, rfl⟩
    have hu := IsLocalizedModule.map_units f' (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
    rw [Module.End.isUnit_iff] at hu ⊢
    have heq : ⇑((algebraMap R (Module.End R N₁)) (r ^ n)) = ⇑((algebraMap S (Module.End S N₁)) (s ^ n)) := by
      funext x; exact hNn n x
    show Function.Bijective ⇑((algebraMap R (Module.End R N₁)) (r ^ n))
    rw [heq]; exact hu
  · intro y
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalizedModule.surj (Submonoid.powers s) f' y
    refine ⟨⟨m, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    rw [Submonoid.smul_def] at e ⊢
    show r ^ n • y = f m
    rw [hNn, hff]; exact e
  · intro m₁ m₂ e
    obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers s) (f := f') (show f' m₁ = f' m₂ by rw [← hff, ← hff, e])
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def] at hc ⊢
    show r ^ n • m₁ = r ^ n • m₂
    rw [hMn, hMn]; exact hc

end Alg
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

section Refine

def sub (e d : Chart p) (g : Γ(V', d.V.1)) (hg : V'.basicOpen g ≤ e.V.1) : Chart p :=
  ⟨e.U, ⟨V'.basicOpen g, d.V.2.basicOpen g⟩, hg.trans e.le⟩

theorem sub_le (e d : Chart p) (g : Γ(V', d.V.1)) (hg : V'.basicOpen g ≤ e.V.1) : sub e d g hg ≤ e := ⟨le_rfl, hg⟩

theorem sub_le' {e d : Chart p} (hed : e ≤ d) (g : Γ(V', d.V.1)) (hg : V'.basicOpen g ≤ e.V.1) : sub e d g hg ≤ d :=
  ⟨hed.1, V'.basicOpen_le g⟩

theorem sub_V (e d : Chart p) (g : Γ(V', d.V.1)) (hg : V'.basicOpen g ≤ e.V.1) : (sub e d g hg).V.1 = V'.basicOpen g := rfl

theorem exists_refinement (d : Chart p) (S : Set (Chart p))
    (hS : ∀ x : V', x ∈ d.V.1 → ∃ e ∈ S, e ≤ d ∧ x ∈ e.V.1) :
    ∃ (κ : Type u) (_ : Fintype κ) (g : κ → Γ(V', d.V.1)) (e : κ → Chart p),
      Ideal.span (Set.range g) = ⊤ ∧ (∀ k, e k ∈ S ∧ e k ≤ d ∧ V'.basicOpen (g k) ≤ (e k).V.1) ∧
      ∀ x : V', x ∈ d.V.1 → ∃ k, x ∈ V'.basicOpen (g k) := by
  classical
  have hpt : ∀ x : d.V.1, ∃ (g : Γ(V', d.V.1)) (e : Chart p),
      e ∈ S ∧ e ≤ d ∧ (x : V') ∈ V'.basicOpen g ∧ V'.basicOpen g ≤ e.V.1 := by
    intro x
    obtain ⟨e, heS, hed, hxe⟩ := hS x.1 x.2
    obtain ⟨g, hgle, hxg⟩ := d.V.2.exists_basicOpen_le ⟨x.1, hxe⟩ x.2
    exact ⟨g, e, heS, hed, hxg, hgle⟩
  choose g e heS hed hxg hge using hpt
  obtain ⟨t, ht⟩ := d.V.2.isCompact.elim_finite_subcover (fun x : d.V.1 => (V'.basicOpen (g x) : Set V'))
    (fun x => (V'.basicOpen (g x)).2) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxg ⟨y, hy⟩⟩)
  refine ⟨↥t, inferInstance, fun k => g k.1, fun k => e k.1, ?_, fun k => ⟨heS k.1, hed k.1, hge k.1⟩, fun y hy => ?_⟩
  swap
  · obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ (V'.basicOpen (g x) : Set V') := by
      simpa only [Set.mem_iUnion, exists_prop] using ht hy
    exact ⟨⟨x, hxt⟩, hyx⟩
  rw [← d.V.2.iSup_basicOpen_eq_self_iff]
  apply le_antisymm
  · exact iSup_le fun f => by
      obtain ⟨i, hi⟩ := f.2
      rw [← hi]
      exact V'.basicOpen_le _
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ (V'.basicOpen (g x) : Set V') := by
      simpa only [Set.mem_iUnion, exists_prop] using ht hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g x, ⟨⟨x, hxt⟩, rfl⟩⟩, hyx⟩

theorem exists_chart_le_le (d d' : Chart p) (x : V') (hx : x ∈ d.V.1) (hx' : x ∈ d'.V.1) :
    ∃ e : Chart p, e ≤ d ∧ e ≤ d' ∧ x ∈ e.V.1 := by
  have hpx : p.base x ∈ d.U.1 ⊓ d'.U.1 := ⟨d.le hx, d'.le hx'⟩
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := p.base x) (U := d.U.1 ⊓ d'.U.1) hpx
  have hx2 : x ∈ (d.V.1 ⊓ d'.V.1) ⊓ p ⁻¹ᵁ W := ⟨⟨hx, hx'⟩, hxW⟩
  obtain ⟨g, hgle, hxg⟩ := d.V.2.exists_basicOpen_le ⟨x, hx2⟩ hx
  refine ⟨⟨⟨W, hW⟩, ⟨V'.basicOpen g, d.V.2.basicOpen g⟩, hgle.trans inf_le_right⟩, ?_, ?_, hxg⟩
  · exact ⟨(Set.Subset.trans hWle inf_le_left : W ≤ d.U.1), V'.basicOpen_le g⟩
  · exact ⟨(Set.Subset.trans hWle inf_le_right : W ≤ d'.U.1), (hgle.trans inf_le_left).trans inf_le_right⟩

end Refine
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

theorem T_ext_of_cover' (hq : G.IsQuasicoherent) (d : Chart p) {κ : Type u} (e : κ → Chart p)
    (he : ∀ k, e k ≤ d) (hcov : d.V.1 ≤ ⨆ k, (e k).V.1) (x y : T p G d)
    (h : ∀ k, tmap (he k) x = tmap (he k) y) : x = y := by
  classical
  obtain ⟨κ', hκ', g, e', hspan, he', -⟩ := exists_refinement d (Set.range e) (fun z hz => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hz)
    exact ⟨e k, ⟨k, rfl⟩, he k, hk⟩)
  have hdk : ∀ k, sub (e' k) d (g k) (he' k).2.2 ≤ d := fun k => sub_le' (he' k).2.1 (g k) (he' k).2.2
  letI inst : ∀ k, Module Γ(V', d.V.1) (T p G (sub (e' k) d (g k) (he' k).2.2)) :=
    fun k => Module.compHom _ (rV (hdk k).2)
  haveI : ∀ k, IsLocalizedModule (Submonoid.powers (g k)) (tmapₗ (p := p) (G := G) (hdk k)) :=
    fun k => tmapₗ_isLocalizedModule' hq (hdk k) (g k) rfl
  refine eq_of_forall_apply_eq g hspan (fun k => tmapₗ (p := p) (G := G) (hdk k)) fun k => ?_
  obtain ⟨k₀, hk₀⟩ := (he' k).1
  have h1 : sub (e' k) d (g k) (he' k).2.2 ≤ e k₀ := by rw [hk₀]; exact sub_le (e' k) d (g k) (he' k).2.2
  show tmap (Chart.le_trans' h1 (he k₀)) x = tmap (Chart.le_trans' h1 (he k₀)) y
  rw [← tmap_tmap h1 (he k₀), ← tmap_tmap h1 (he k₀), h k₀]

theorem Sec.ext_of_cover' (hq : G.IsQuasicoherent) {W : V'.Opens} (s t : Sec p G W) {ι : Type u}
    (c : ι → Chart p) (hc : ∀ i, (c i).V.1 ≤ W) (hcov : W ≤ ⨆ i, (c i).V.1)
    (h : ∀ i, s.1 ⟨c i, hc i⟩ = t.1 ⟨c i, hc i⟩) : s = t := by
  apply Sec.ext'
  intro c₀
  let κ : Type u := {e : Chart p // e ≤ c₀.1 ∧ ∃ i, e ≤ c i}
  refine T_ext_of_cover' hq c₀.1 (fun e : κ => e.1) (fun e => e.2.1) ?_ (s.1 c₀) (t.1 c₀) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov (c₀.2 hx))
    obtain ⟨e, he₀, hei, hxe⟩ := exists_chart_le_le c₀.1 (c i) x hx hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨e, he₀, i, hei⟩, hxe⟩
  · intro e
    obtain ⟨i, hei⟩ := e.2.2
    have heW : e.1.V.1 ≤ W := e.2.1.2.trans c₀.2
    rw [Sec.compat s ⟨e.1, heW⟩ c₀ e.2.1, Sec.compat t ⟨e.1, heW⟩ c₀ e.2.1,
      ← Sec.compat s ⟨e.1, heW⟩ ⟨c i, hc i⟩ hei, ← Sec.compat t ⟨e.1, heW⟩ ⟨c i, hc i⟩ hei, h i]

theorem Sec.exists_of_cover' (hq : G.IsQuasicoherent) {W : V'.Opens} {ι : Type u}
    (c : ι → Chart p) (hc : ∀ i, (c i).V.1 ≤ W) (hcov : W ≤ ⨆ i, (c i).V.1)
    (t : ∀ i, T p G (c i))
    (hcompat : ∀ (i j : ι) (d : Chart p) (hi : d ≤ c i) (hj : d ≤ c j), tmap hi (t i) = tmap hj (t j)) :
    ∃ s : Sec p G W, ∀ i, s.1 ⟨c i, hc i⟩ = t i := by
  classical

  let Good : (c₀ : Chart p) → T p G c₀ → Prop := fun c₀ m =>
    ∀ (e : Chart p) (i : ι) (he : e ≤ c₀) (hei : e ≤ c i), tmap he m = tmap hei (t i)
  have huniq : ∀ (c₀ : Chart p), c₀.V.1 ≤ W → ∀ m m', Good c₀ m → Good c₀ m' → m = m' := by
    intro c₀ hc₀ m m' hm hm'
    let κ : Type u := {e : Chart p // e ≤ c₀ ∧ ∃ i, e ≤ c i}
    refine T_ext_of_cover' hq c₀ (fun e : κ => e.1) (fun e => e.2.1) ?_ m m' ?_
    · intro x hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov (hc₀ hx))
      obtain ⟨e, he₀, hei, hxe⟩ := exists_chart_le_le c₀ (c i) x hx hi
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨e, he₀, i, hei⟩, hxe⟩
    · intro e
      obtain ⟨i, hei⟩ := e.2.2
      rw [hm e.1 i e.2.1 hei, hm' e.1 i e.2.1 hei]
  have hgood_tmap : ∀ (c₁ c₂ : Chart p) (h : c₁ ≤ c₂) (m : T p G c₂), Good c₂ m → Good c₁ (tmap h m) := by
    intro c₁ c₂ h m hm e i he hei
    rw [tmap_tmap, hm e i (Chart.le_trans' he h) hei]
  have hgood_t : ∀ i, Good (c i) (t i) := fun i e j he hej => hcompat i j e he hej

  have hex : ∀ c₀ : Chart p, c₀.V.1 ≤ W → ∃ m, Good c₀ m := by
    intro c₀ hc₀
    obtain ⟨κ, hκ, g, e', hspan, he', hcovg⟩ := exists_refinement c₀ {e | ∃ i, e ≤ c i} (fun x hx => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov (hc₀ hx))
      obtain ⟨e, he₀, hei, hxe⟩ := exists_chart_le_le c₀ (c i) x hx hi
      exact ⟨e, ⟨i, hei⟩, he₀, hxe⟩)
    choose idx hidx using fun k => (he' k).1

    have hgk : ∀ k, V'.basicOpen (g k) ≤ c₀.V.1 := fun k => V'.basicOpen_le _
    let ĉ : κ → Chart p := fun k => sub c₀ c₀ (g k) (hgk k)
    have hĉ : ∀ k, ĉ k ≤ c₀ := fun k => sub_le' (Chart.le_rfl c₀) (g k) (hgk k)
    have hd' : ∀ k, (ĉ k).V.1 ≤ p ⁻¹ᵁ (e' k).U.1 := fun k => (he' k).2.2.trans (e' k).le
    let d : κ → Chart p := fun k => shrink (ĉ k) (e' k).U (hd' k)
    have hdĉ : ∀ k, d k ≤ ĉ k := fun k => shrink_le (ĉ k) (e' k).U (he' k).2.1.1 (hd' k)
    have hdi : ∀ k, d k ≤ c (idx k) := fun k => ⟨(hidx k).1, (he' k).2.2.trans (hidx k).2⟩
    let v : ∀ k, T p G (d k) := fun k => tmap (hdi k) (t (idx k))
    have hbij : ∀ k, Function.Bijective (tmap (G := G) (hdĉ k)) :=
      fun k => tmap_shrink_bijective hq (ĉ k) (e' k).U (he' k).2.1.1 (hd' k)
    choose w hw using fun k => (hbij k).2 (v k)
    have hgkl : ∀ k l, V'.basicOpen (g k * g l) ≤ c₀.V.1 := fun k l => V'.basicOpen_le _
    let ĉ₂ : κ → κ → Chart p := fun k l => sub c₀ c₀ (g k * g l) (hgkl k l)
    have h₂k : ∀ k l, ĉ₂ k l ≤ ĉ k := fun k l =>
      ⟨le_rfl, by show V'.basicOpen (g k * g l) ≤ V'.basicOpen (g k); rw [Scheme.basicOpen_mul]; exact inf_le_left⟩
    have h₂l : ∀ k l, ĉ₂ k l ≤ ĉ l := fun k l =>
      ⟨le_rfl, by show V'.basicOpen (g k * g l) ≤ V'.basicOpen (g l); rw [Scheme.basicOpen_mul]; exact inf_le_right⟩
    have h₂c : ∀ k l, ĉ₂ k l ≤ c₀ := fun k l => Chart.le_trans' (h₂k k l) (hĉ k)

    letI instN : ∀ k, Module Γ(V', c₀.V.1) (T p G (ĉ k)) := fun k => Module.compHom _ (rV (hĉ k).2)
    letI instN₂ : ∀ k l, Module Γ(V', c₀.V.1) (T p G (ĉ₂ k l)) := fun k l => Module.compHom _ (rV (h₂c k l).2)
    haveI : ∀ k, IsLocalizedModule (Submonoid.powers (g k)) (tmapₗ (p := p) (G := G) (hĉ k)) :=
      fun k => tmapₗ_isLocalizedModule' hq (hĉ k) (g k) rfl
    let l : ∀ k l, T p G (ĉ k) →ₗ[Γ(V', c₀.V.1)] T p G (ĉ₂ k l) := fun k l =>
      { toFun := tmap (h₂k k l), map_add' := map_add _, map_smul' := fun r x => by
          show tmap (h₂k k l) (rV (hĉ k).2 r • x) = rV (h₂c k l).2 r • tmap (h₂k k l) x
          rw [tmap_smul, rV_rV] }
    let l' : ∀ k l, T p G (ĉ l) →ₗ[Γ(V', c₀.V.1)] T p G (ĉ₂ k l) := fun k l =>
      { toFun := tmap (h₂l k l), map_add' := map_add _, map_smul' := fun r x => by
          show tmap (h₂l k l) (rV (hĉ l).2 r • x) = rV (h₂c k l).2 r • tmap (h₂l k l) x
          rw [tmap_smul, rV_rV] }
    haveI : ∀ k l₀, IsLocalizedModule (Submonoid.powers (g l₀)) (l k l₀) := by
      intro k l₀
      letI : Module Γ(V', (ĉ k).V.1) (T p G (ĉ₂ k l₀)) := Module.compHom _ (rV (h₂k k l₀).2)
      have hV : (ĉ₂ k l₀).V.1 = V'.basicOpen (rV (hĉ k).2 (g l₀)) := by
        show V'.basicOpen (g k * g l₀) = V'.basicOpen ((V'.presheaf.map (homOfLE (hĉ k).2).op).hom (g l₀))
        rw [Scheme.basicOpen_mul, Scheme.basicOpen_res]
        rfl
      haveI := tmapₗ_isLocalizedModule' hq (h₂k k l₀) (rV (hĉ k).2 (g l₀)) hV
      exact isLocalizedModule_of_smul_eq (l k l₀) (tmapₗ (h₂k k l₀)) (fun m => rfl) (g l₀) (rV (hĉ k).2 (g l₀))
        (fun m => rfl) (fun n => by
          show rV (h₂c k l₀).2 (g l₀) • n = rV (h₂k k l₀).2 (rV (hĉ k).2 (g l₀)) • n
          rw [rV_rV])
    have hll : ∀ k l₀, l k l₀ ∘ₗ tmapₗ (hĉ k) = l' k l₀ ∘ₗ tmapₗ (hĉ l₀) := fun k l₀ => by
      apply LinearMap.ext
      intro x
      show tmap (h₂k k l₀) (tmap (hĉ k) x) = tmap (h₂l k l₀) (tmap (hĉ l₀) x)
      rw [tmap_tmap, tmap_tmap]

    have hx : ∀ k l₀, l k l₀ (w k) = l' k l₀ (w l₀) := by
      intro k l₀
      show tmap (h₂k k l₀) (w k) = tmap (h₂l k l₀) (w l₀)
      let κ' : Type u := {e : Chart p // e ≤ d k ∧ e ≤ d l₀}
      have heĉ₂ : ∀ e : κ', e.1 ≤ ĉ₂ k l₀ := fun e =>
        ⟨e.2.1.1.trans (he' k).2.1.1, by
          show e.1.V.1 ≤ V'.basicOpen (g k * g l₀)
          rw [Scheme.basicOpen_mul]
          exact le_inf e.2.1.2 e.2.2.2⟩
      refine T_ext_of_cover' hq (ĉ₂ k l₀) (fun e : κ' => e.1) heĉ₂ ?_ _ _ ?_
      · intro x hx
        have hx' : x ∈ V'.basicOpen (g k) ⊓ V'.basicOpen (g l₀) := by
          rw [← Scheme.basicOpen_mul]; exact hx
        obtain ⟨e, hek, hel, hxe⟩ := exists_chart_le_le (d k) (d l₀) x hx'.1 hx'.2
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨e, hek, hel⟩, hxe⟩
      · intro e
        rw [tmap_tmap, tmap_tmap,
          show tmap (Chart.le_trans' (heĉ₂ e) (h₂k k l₀)) (w k) = tmap e.2.1 (tmap (hdĉ k) (w k)) from
            (tmap_tmap _ _ _).symm,
          show tmap (Chart.le_trans' (heĉ₂ e) (h₂l k l₀)) (w l₀) = tmap e.2.2 (tmap (hdĉ l₀) (w l₀)) from
            (tmap_tmap _ _ _).symm,
          hw, hw, tmap_tmap, tmap_tmap]
        exact hcompat _ _ _ _ _
    obtain ⟨m, hm⟩ := IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top g hspan
      (fun k => tmapₗ (p := p) (G := G) (hĉ k)) l l' hll w hx
    refine ⟨m, fun e i he hei => ?_⟩

    let κ'' : Type u := {e'' : Chart p // e'' ≤ e ∧ ∃ k, e'' ≤ d k}
    refine T_ext_of_cover' hq e (fun e'' : κ'' => e''.1) (fun e'' => e''.2.1) ?_ _ _ ?_
    · intro x hx
      obtain ⟨k, hk⟩ := hcovg x (he.2 hx)
      obtain ⟨e'', h1, h2, hx''⟩ := exists_chart_le_le e (d k) x hx hk
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨e'', h1, k, h2⟩, hx''⟩
    · intro e''
      obtain ⟨k, hk⟩ := e''.2.2
      rw [tmap_tmap, tmap_tmap,
        show tmap (Chart.le_trans' e''.2.1 he) m = tmap (Chart.le_trans' hk (hdĉ k)) (tmap (hĉ k) m) from
          (tmap_tmap _ _ _).symm]
      have hmk : tmap (hĉ k) m = w k := hm k
      rw [hmk, show tmap (Chart.le_trans' hk (hdĉ k)) (w k) = tmap hk (tmap (hdĉ k) (w k)) from
        (tmap_tmap _ _ _).symm, hw, tmap_tmap]
      exact hcompat _ _ _ _ _
  choose sval hsval using fun c₀ : ChartIn p W => hex c₀.1 c₀.2
  refine ⟨⟨fun c₀ => sval c₀, fun c₁ c₂ hle => ?_⟩, fun i => ?_⟩
  · exact huniq c₁.1 c₁.2 _ _ (hgood_tmap _ _ hle _ (hsval c₂)) (hsval c₁)
  · exact huniq (c i) (hc i) _ _ (hsval ⟨c i, hc i⟩) (hgood_t i)

theorem evₗ_bijective' (hq : G.IsQuasicoherent) (c : Chart p) : Function.Bijective (evₗ (p := p) (G := G) c) := by
  constructor
  · intro s t h
    exact Sec.ext_of_cover' hq s t (fun _ : PUnit.{u+1} => c) (fun _ => le_rfl)
      (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨PUnit.unit, hx⟩) (fun _ => h)
  · intro t
    obtain ⟨s, hs⟩ := Sec.exists_of_cover' hq (W := c.V.1) (fun _ : PUnit.{u+1} => c) (fun _ => le_rfl)
      (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨PUnit.unit, hx⟩) (fun _ => t) (fun i j d hi hj => rfl)
    exact ⟨s, hs PUnit.unit⟩

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

end P1Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

namespace P1Sol

noncomputable section

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
variable {p : V' ⟶ P} {G : OModulePresheaf q}

theorem evₗ_bijective (hq : G.IsQuasicoherent) (c : Chart p) : Function.Bijective (evₗ (p := p) (G := G) c) := evₗ_bijective' hq c

def evEquiv (hq : G.IsQuasicoherent) (c : Chart p) : Sec p G c.V.1 ≃ₗ[Γ(V', c.V.1)] T p G c :=
  LinearEquiv.ofBijective (evₗ c) (evₗ_bijective hq c)

theorem evEquiv_apply (hq : G.IsQuasicoherent) (c : Chart p) (s : Sec p G c.V.1) :
    evEquiv hq c s = s.1 ⟨c, le_rfl⟩ := rfl

theorem φ_algebraMap_eq_sc (c : Chart p) (r : A) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q c.U.1
    c.φ (algebraMap A Γ(P, c.U.1) r) = sc p q c.V.1 r := by
  show (q.appLE ⊤ c.U.1 le_top ≫ p.appLE c.U.1 c.V.1 c.le).hom _ = ((p ≫ q).appLE ⊤ c.V.1 le_top).hom _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

def eta (hq : G.IsQuasicoherent) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) :
    letI := Sec.moduleA (p := p) (G := G) V.1
    G.obj U.1 →ₗ[A] Sec p G V.1 :=
  letI := Sec.moduleA (p := p) (G := G) V.1
  letI := (p.appLE U.1 V.1 h).hom.toAlgebra
  { toFun := fun x => (evEquiv hq ⟨U, V, h⟩).symm ((1 : Γ(V', V.1)) ⊗ₜ[Chart.RU (⟨U, V, h⟩ : Chart p)] x)
    map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
    map_smul' := fun r x => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1
      have hx : r • x = (algebraMap A Γ(P, U.1) r) • x := (algebraMap_smul _ r x).symm
      rw [hx, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have e1 : algebraMap Γ(P, U.1) Γ(V', V.1) (algebraMap A Γ(P, U.1) r) = sc p q V.1 r :=
        φ_algebraMap_eq_sc (p := p) ⟨U, V, h⟩ r
      have e2 : sc p q V.1 r ⊗ₜ[Chart.RU (⟨U, V, h⟩ : Chart p)] x =
          sc p q V.1 r • ((1 : Γ(V', V.1)) ⊗ₜ[Chart.RU (⟨U, V, h⟩ : Chart p)] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e2, map_smul]
      rfl }

theorem evEquiv_eta (hq : G.IsQuasicoherent) (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1)
    (x : G.obj U.1) :
    letI := (p.appLE U.1 V.1 h).hom.toAlgebra
    evEquiv hq ⟨U, V, h⟩ (eta hq U V h x) = (1 : Γ(V', V.1)) ⊗ₜ[Chart.RU (⟨U, V, h⟩ : Chart p)] x :=
  (evEquiv hq ⟨U, V, h⟩).apply_symm_apply _

theorem tmapₗ_isLocalizedModule (hq : G.IsQuasicoherent) {c₁ c₂ : Chart p} (h : c₁ ≤ c₂)
    (g : Γ(V', c₂.V.1)) (hV : c₁.V.1 = V'.basicOpen g) :
    letI : Module Γ(V', c₂.V.1) (T p G c₁) := Module.compHom (T p G c₁) (rV h.2)
    IsLocalizedModule (Submonoid.powers g) (tmapₗ (p := p) (G := G) h) := tmapₗ_isLocalizedModule' hq h g hV

theorem T_ext_of_cover (hq : G.IsQuasicoherent) (d : Chart p) {κ : Type u} (e : κ → Chart p)
    (he : ∀ k, e k ≤ d) (hcov : d.V.1 ≤ ⨆ k, (e k).V.1) (x y : T p G d)
    (h : ∀ k, tmap (he k) x = tmap (he k) y) : x = y := T_ext_of_cover' hq d e he hcov x y h

theorem Sec.ext_of_cover (hq : G.IsQuasicoherent) {W : V'.Opens} (s t : Sec p G W) {ι : Type u}
    (c : ι → Chart p) (hc : ∀ i, (c i).V.1 ≤ W) (hcov : W ≤ ⨆ i, (c i).V.1)
    (h : ∀ i, s.1 ⟨c i, hc i⟩ = t.1 ⟨c i, hc i⟩) : s = t := Sec.ext_of_cover' hq s t c hc hcov h

theorem Sec.exists_of_cover (hq : G.IsQuasicoherent) {W : V'.Opens} {ι : Type u}
    (c : ι → Chart p) (hc : ∀ i, (c i).V.1 ≤ W) (hcov : W ≤ ⨆ i, (c i).V.1)
    (t : ∀ i, T p G (c i))
    (hcompat : ∀ (i j : ι) (d : Chart p) (hi : d ≤ c i) (hj : d ≤ c j), tmap hi (t i) = tmap hj (t j)) :
    ∃ s : Sec p G W, ∀ i, s.1 ⟨c i, hc i⟩ = t i := Sec.exists_of_cover' hq c hc hcov t hcompat

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

end P1Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

namespace P1Sol
namespace Big

theorem exists_finite_chartBasic_cover_le {P V' : Scheme.{u}} (p : V' ⟶ P) (V : V'.affineOpens)
    (O : P.Opens) (hO : V.1 ≤ p ⁻¹ᵁ O) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → Γ(V', V.1)) (U : ι → P.affineOpens),
      Ideal.span (Set.range g) = ⊤ ∧ (∀ i, V'.basicOpen (g i) ≤ p ⁻¹ᵁ (U i).1) ∧ ∀ i, (U i).1 ≤ O := by
  classical
  have hpt : ∀ x : V.1, ∃ (g : Γ(V', V.1)) (U : P.affineOpens),
      (x : V') ∈ V'.basicOpen g ∧ V'.basicOpen g ≤ p ⁻¹ᵁ U.1 ∧ U.1 ≤ O := by
    intro x
    obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := p.base x.1) (U := O) (hO x.2)
    have hx' : (x : V') ∈ V.1 ⊓ p ⁻¹ᵁ W := ⟨x.2, hxW⟩
    obtain ⟨g, hgle, hxg⟩ := V.2.exists_basicOpen_le ⟨x.1, hx'⟩ x.2
    exact ⟨g, ⟨W, hW⟩, hxg, hgle.trans inf_le_right, hWO⟩
  choose g U hxg hgU hUO using hpt
  obtain ⟨t, ht⟩ := V.2.isCompact.elim_finite_subcover (fun x : V.1 => (V'.basicOpen (g x) : Set V'))
    (fun x => (V'.basicOpen (g x)).2) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxg ⟨y, hy⟩⟩)
  refine ⟨↥t, inferInstance, fun i => g i.1, fun i => U i.1, ?_, fun i => hgU i.1, fun i => hUO i.1⟩
  rw [← V.2.iSup_basicOpen_eq_self_iff]
  apply le_antisymm
  · exact iSup_le fun f => by
      obtain ⟨i, hi⟩ := f.2
      rw [← hi]
      exact V'.basicOpen_le _
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, y ∈ (V'.basicOpen (g x) : Set V') := by
      simpa only [Set.mem_iUnion, exists_prop] using ht hy
    exact Opens.mem_iSup.mpr ⟨⟨g x, ⟨⟨x, hxt⟩, rfl⟩⟩, hyx⟩

theorem exists_finite_chartBasic_cover {P V' : Scheme.{u}} (p : V' ⟶ P) (V : V'.affineOpens) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → Γ(V', V.1)) (U : ι → P.affineOpens),
      Ideal.span (Set.range g) = ⊤ ∧ ∀ i, V'.basicOpen (g i) ≤ p ⁻¹ᵁ (U i).1 := by
  obtain ⟨ι, hι, g, U, h1, h2, -⟩ := exists_finite_chartBasic_cover_le p V ⊤ (by simp)
  exact ⟨ι, hι, g, U, h1, h2⟩

theorem le_iSup_basicOpen_of_span_eq_top {V' : Scheme.{u}} (V : V'.affineOpens) {ι : Type u} (g : ι → Γ(V', V.1))
    (h : Ideal.span (Set.range g) = ⊤) : V.1 ≤ ⨆ i, V'.basicOpen (g i) := by
  rw [← V.2.iSup_basicOpen_eq_self_iff] at h
  intro x hx
  rw [← h] at hx
  obtain ⟨f, hf⟩ := Opens.mem_iSup.mp hx
  obtain ⟨i, hi⟩ := f.2
  exact Opens.mem_iSup.mpr ⟨i, by rw [hi]; exact hf⟩

theorem exists_forall_ge_of_finite {ι : Type u} [Finite ι] {P : ι → ℕ → Prop}
    (hmono : ∀ i m n, m ≤ n → P i m → P i n) (h : ∀ i, ∃ n, P i n) : ∃ N, ∀ i, P i N := by
  classical
  haveI := Fintype.ofFinite ι
  choose n hn using h
  exact ⟨Finset.univ.sup n, fun i => hmono i _ _ (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

end P1Sol.Big
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

namespace P1Sol
namespace Big

theorem bijective_one_tmul_of_bijective_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Bijective (algebraMap R S)) (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Bijective (fun x : M => (1 : S) ⊗ₜ[R] x) := by
  let e' : R ≃ₐ[R] S := AlgEquiv.ofBijective (Algebra.ofId R S) h
  let Φ : M ≃ₗ[R] S ⊗[R] M :=
    (TensorProduct.lid R M).symm ≪≫ₗ TensorProduct.congr e'.toLinearEquiv (LinearEquiv.refl R M)
  have hΦ : (fun x : M => (1 : S) ⊗ₜ[R] x) = Φ := by
    funext x
    simp only [Φ, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, map_one]
  rw [hΦ]
  exact Φ.bijective

theorem bijective_appLE_of_isIso_morphismRestrict {P V' : Scheme.{u}} (p : V' ⟶ P) (W : P.Opens) (W' : V'.Opens)
    (hW : W' = p ⁻¹ᵁ W) [IsIso (p ∣_ W)] : Function.Bijective (p.appLE W W' hW.le) := by
  have h1 : IsIso ((p ∣_ W).app ⊤) := inferInstance
  rw [morphismRestrict_app'] at h1
  have h2 : IsIso (p.appLE W W' hW.le) := by
    refine (Scheme.Hom.appLE_congr p _ ?_ ?_ (fun φ => IsIso φ)).mp h1
    · exact W.ι_image_top
    · rw [hW, Scheme.Hom.preimage_top]
      exact (p ⁻¹ᵁ W).ι_image_top
  exact ConcreteCategory.bijective_of_isIso (p.appLE W W' hW.le)

end P1Sol.Big
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

namespace P1Sol
namespace Big

variable {A : Type u} [CommRing A] {P V' : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
variable (p : V' ⟶ P) (G : OModulePresheaf q)

theorem eta_bijective_of_isIso
    (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1) [IsIso (p ∣_ W.1)]
    {E : Type u} (η : G.obj W.1 → E)
    (ev : E ≃ T p G ⟨W, W', hW.le⟩)
    (hη : letI := chartAlgebra p ⟨W, W', hW.le⟩
      ∀ x : G.obj W.1, ev (η x) = (1 : Γ(V', W'.1)) ⊗ₜ[Γ(P, W.1)] x) :
    Function.Bijective η := by
  letI := chartAlgebra p ⟨W, W', hW.le⟩
  have hφ : Function.Bijective (algebraMap Γ(P, W.1) Γ(V', W'.1)) :=
    bijective_appLE_of_isIso_morphismRestrict p W.1 W'.1 hW
  have h1 := bijective_one_tmul_of_bijective_algebraMap hφ (G.obj W.1)
  have hcomp : η = ev.symm ∘ (fun x : G.obj W.1 => (1 : Γ(V', W'.1)) ⊗ₜ[Γ(P, W.1)] x) := by
    funext x
    apply ev.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, hη]
  rw [hcomp]
  exact ev.symm.bijective.comp h1

theorem eta_bijective (hq : G.IsQuasicoherent)
    (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1) (hiso : IsIso (p ∣_ W.1)) :
    Function.Bijective (eta (p := p) (G := G) hq W W' hW.le) := by
  haveI := hiso
  exact eta_bijective_of_isIso p G W W' hW (eta hq W W' hW.le) (evEquiv hq ⟨W, W', hW.le⟩).toEquiv
    (fun x => evEquiv_eta hq W W' hW.le x)

theorem finite_T (hG : G.IsCoherent) (c : Chart p) : Module.Finite Γ(V', c.V.1) (T p G c) := by
  haveI : Module.Finite Γ(P, c.U.1) (G.obj c.U.1) := hG c.U
  infer_instance

theorem isCoherent (hq : G.IsQuasicoherent) (hq' : (pullbackDatum p G).IsQuasicoherent) (hG : G.IsCoherent) :
    (pullbackDatum p G).IsCoherent := by
  classical
  intro V
  obtain ⟨ι, hι, g, U, hspan, hgU⟩ := exists_finite_chartBasic_cover p V

  have hfin : ∀ i, Module.Finite Γ(V', V'.basicOpen (g i)) ((pullbackDatum p G).obj (V'.basicOpen (g i))) := by
    intro i
    let c : Chart p := ⟨U i, ⟨V'.basicOpen (g i), V.2.basicOpen (g i)⟩, hgU i⟩
    haveI := finite_T p G hG c
    exact Module.Finite.equiv (evEquiv hq c).symm

  letI instM : ∀ g' : ↥(Set.range g), Module Γ(V', V.1) ((pullbackDatum p G).obj (V'.basicOpen g'.1)) :=
    fun g' => (pullbackDatum p G).moduleRestrict (V'.basicOpen_le g'.1)
  haveI : ∀ g' : ↥(Set.range g),
      IsScalarTower Γ(V', V.1) Γ(V', V'.basicOpen g'.1) ((pullbackDatum p G).obj (V'.basicOpen g'.1)) :=
    fun g' => IsScalarTower.of_algebraMap_smul fun r m => rfl
  haveI : ∀ g' : ↥(Set.range g), IsLocalization.Away g'.1 Γ(V', V'.basicOpen g'.1) :=
    fun g' => V.2.isLocalization_basicOpen g'.1
  haveI : ∀ g' : ↥(Set.range g),
      IsLocalizedModule.Away g'.1 ((pullbackDatum p G).resₗ (V'.basicOpen_le g'.1)) :=
    fun g' => (pullbackDatum p G).isLocalizedModule_res_of_isQuasicoherent hq' V g'.1
  refine Module.Finite.of_localizationSpan' (Set.range g) hspan
    (Mₚ := fun g' : ↥(Set.range g) => (pullbackDatum p G).obj (V'.basicOpen g'.1))
    (Rₚ := fun g' : ↥(Set.range g) => Γ(V', V'.basicOpen g'.1))
    (fun g' => (pullbackDatum p G).resₗ (V'.basicOpen_le g'.1)) ?_
  rintro ⟨_, i, rfl⟩
  exact hfin i

theorem eta_smul (hq : G.IsQuasicoherent)
    (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G.obj U.1) :
    eta (p := p) (G := G) hq U V h (a • x) = (p.appLE U.1 V.1 h).hom a • eta hq U V h x := by
  letI := chartAlgebra p ⟨U, V, h⟩
  apply (evEquiv hq ⟨U, V, h⟩).injective
  rw [evEquiv_eta, map_smul, evEquiv_eta, TensorProduct.tmul_smul, ← algebraMap_smul (Γ(V', V.1)) a]
  rfl

theorem eta_res (hq : G.IsQuasicoherent)
    (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
    (hV : V₁.1 ≤ V₂.1) (x : G.obj U.1) :
    (pullbackDatum p G).res hV (eta hq U V₂ h₂ x) = eta hq U V₁ h₁ x := by
  apply (evEquiv hq ⟨U, V₁, h₁⟩).injective
  have hle : (⟨U, V₁, h₁⟩ : Chart p) ≤ ⟨U, V₂, h₂⟩ := ⟨le_rfl, hV⟩
  rw [evEquiv_eta]
  show evₗ (⟨U, V₁, h₁⟩ : Chart p) ((pullbackDatum p G).res hle.2 (eta hq U V₂ h₂ x)) = _
  rw [evₗ_res hle, show evₗ (⟨U, V₂, h₂⟩ : Chart p) (eta hq U V₂ h₂ x) = evEquiv hq ⟨U, V₂, h₂⟩ (eta hq U V₂ h₂ x) from rfl,
    evEquiv_eta, tmap_tmul, map_one, G.res_refl_apply]

theorem eta_resU (hq : G.IsQuasicoherent)
    (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
    (hU : U₁.1 ≤ U₂.1) (x : G.obj U₂.1) :
    eta (p := p) (G := G) hq U₂ V h₂ x = eta hq U₁ V h₁ (G.res hU x) := by
  apply (evEquiv hq ⟨U₁, V, h₁⟩).injective
  have hle : (⟨U₁, V, h₁⟩ : Chart p) ≤ ⟨U₂, V, h₂⟩ := ⟨hU, le_rfl⟩
  rw [evEquiv_eta, evEquiv_apply]
  rw [← Sec.compat (eta hq U₂ V h₂ x) ⟨⟨U₁, V, h₁⟩, le_rfl⟩ ⟨⟨U₂, V, h₂⟩, le_rfl⟩ hle,
    show (eta hq U₂ V h₂ x).1 ⟨⟨U₂, V, h₂⟩, le_rfl⟩ = evEquiv hq ⟨U₂, V, h₂⟩ (eta hq U₂ V h₂ x) from rfl,
    evEquiv_eta, tmap_tmul, rV_refl]

theorem exists_beta (hq : G.IsQuasicoherent)
    (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) :
    letI := (p.appLE U.1 V.1 h).hom.toAlgebra
    ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G.obj U.1 ≃ₗ[Γ(V', V.1)] (pullbackDatum p G).obj V.1,
      ∀ x : G.obj U.1, β (1 ⊗ₜ x) = eta hq U V h x := by
  refine ⟨(evEquiv hq ⟨U, V, h⟩).symm, fun x => ?_⟩
  exact (LinearEquiv.symm_apply_eq _).mpr (evEquiv_eta hq U V h x).symm

section QC

variable {p G}

def bchart (U : P.affineOpens) (V : V'.affineOpens) (g : Γ(V', V.1)) (h : V'.basicOpen g ≤ p ⁻¹ᵁ U.1) : Chart p :=
  ⟨U, ⟨V'.basicOpen g, V.2.basicOpen g⟩, h⟩

theorem bchart_V (U : P.affineOpens) (V : V'.affineOpens) (g : Γ(V', V.1)) (h : V'.basicOpen g ≤ p ⁻¹ᵁ U.1) :
    (bchart (p := p) U V g h).V.1 = V'.basicOpen g := rfl

def cut (c : Chart p) {W : V'.Opens} (hc : c.V.1 ≤ W) (f : Γ(V', W)) : Chart p :=
  ⟨c.U, ⟨V'.basicOpen (rV hc f), c.V.2.basicOpen _⟩, (V'.basicOpen_le _).trans c.le⟩

theorem cut_le (c : Chart p) {W : V'.Opens} (hc : c.V.1 ≤ W) (f : Γ(V', W)) : cut c hc f ≤ c :=
  ⟨le_rfl, V'.basicOpen_le _⟩

theorem cut_V (c : Chart p) {W : V'.Opens} (hc : c.V.1 ≤ W) (f : Γ(V', W)) :
    (cut c hc f).V.1 = c.V.1 ⊓ V'.basicOpen f := by
  show V'.basicOpen (rV hc f) = _
  exact Scheme.basicOpen_res _ _ _

theorem cut_V_le (c : Chart p) {W : V'.Opens} (hc : c.V.1 ≤ W) (f : Γ(V', W)) :
    (cut c hc f).V.1 ≤ V'.basicOpen f := by rw [cut_V]; exact inf_le_right

theorem cut_isLocalizedModule (hq : G.IsQuasicoherent) (c : Chart p) {W : V'.Opens} (hc : c.V.1 ≤ W) (f : Γ(V', W)) :
    letI : Module Γ(V', c.V.1) (T p G (cut c hc f)) := Module.compHom _ (rV (cut_le c hc f).2)
    IsLocalizedModule (Submonoid.powers (rV hc f)) (tmapₗ (p := p) (G := G) (cut_le c hc f)) :=
  tmapₗ_isLocalizedModule hq (cut_le c hc f) (rV hc f) rfl

theorem exists_pow_smul_eq_zero_of_tmap_cut_eq_zero (hq : G.IsQuasicoherent) (c : Chart p) {W : V'.Opens}
    (hc : c.V.1 ≤ W) (f : Γ(V', W)) (t : T p G c) (ht : tmap (cut_le c hc f) t = 0) :
    ∃ n : ℕ, (rV hc f) ^ n • t = 0 := by
  letI : Module Γ(V', c.V.1) (T p G (cut c hc f)) := Module.compHom _ (rV (cut_le c hc f).2)
  haveI := cut_isLocalizedModule (p := p) (G := G) hq c hc f
  have ht' : tmapₗ (p := p) (G := G) (cut_le c hc f) t = 0 := ht
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (rV hc f))
    (f := tmapₗ (p := p) (G := G) (cut_le c hc f))).mp ht'
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
  exact ⟨n, hst⟩

theorem exists_tmap_cut_eq_pow_smul (hq : G.IsQuasicoherent) (c : Chart p) {W : V'.Opens}
    (hc : c.V.1 ≤ W) (f : Γ(V', W)) (x : T p G (cut c hc f)) :
    ∃ (n : ℕ) (t : T p G c), tmap (cut_le c hc f) t = rV ((cut_le c hc f).2.trans hc) (f ^ n) • x := by
  letI : Module Γ(V', c.V.1) (T p G (cut c hc f)) := Module.compHom _ (rV (cut_le c hc f).2)
  haveI := cut_isLocalizedModule (p := p) (G := G) hq c hc f
  obtain ⟨⟨t, ⟨s, hs⟩⟩, hst⟩ := IsLocalizedModule.surj (Submonoid.powers (rV hc f))
    (tmapₗ (p := p) (G := G) (cut_le c hc f)) x
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
  refine ⟨n, t, ?_⟩
  have : tmap (cut_le c hc f) t = rV (cut_le c hc f).2 ((rV hc f) ^ n) • x := hst.symm
  rw [this, map_pow, rV_rV, map_pow]

theorem pow_smul_eq_zero_of_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r : R) (t : M)
    {m n : ℕ} (hmn : m ≤ n) (h : r ^ m • t = 0) : r ^ n • t = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, pow_add, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero (hq : G.IsQuasicoherent) (V : V'.affineOpens) (f : Γ(V', V.1)) (y : (pullbackDatum p G).obj V.1)
    (hy : (pullbackDatum p G).res (V'.basicOpen_le f) y = 0) : ∃ n : ℕ, (f ^ n : Γ(V', V.1)) • y = 0 := by
  classical
  obtain ⟨ι, hι, g, U, hspan, hgU⟩ := exists_finite_chartBasic_cover p V
  let c : ι → Chart p := fun i => bchart (U i) V (g i) (hgU i)
  have hcV : ∀ i, (c i).V.1 ≤ V.1 := fun i => V'.basicOpen_le (g i)
  have hcovV : V.1 ≤ ⨆ i, (c i).V.1 := le_iSup_basicOpen_of_span_eq_top V g hspan

  have hloc : ∀ i, ∃ n : ℕ, (rV (hcV i) f) ^ n • y.1 ⟨c i, hcV i⟩ = 0 := by
    intro i
    apply exists_pow_smul_eq_zero_of_tmap_cut_eq_zero hq (c i) (hcV i) f
    rw [Sec.compat y ⟨cut (c i) (hcV i) f, (cut_le _ _ _).2.trans (hcV i)⟩ ⟨c i, hcV i⟩ (cut_le _ _ _)]
    have := congrArg (fun s : Sec p G (V'.basicOpen f) => s.1 ⟨cut (c i) (hcV i) f, cut_V_le _ _ _⟩) hy
    exact this
  obtain ⟨N, hN⟩ := exists_forall_ge_of_finite (P := fun i n => (rV (hcV i) f) ^ n • y.1 ⟨c i, hcV i⟩ = 0)
    (fun i m n hmn h => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [add_comm, pow_add, mul_smul, h, smul_zero]) hloc
  refine ⟨N, Sec.ext_of_cover hq _ _ c hcV hcovV fun i => ?_⟩
  have h1 : ((f ^ N • y : Sec p G V.1)).1 ⟨c i, hcV i⟩ = rV (hcV i) (f ^ N) • y.1 ⟨c i, hcV i⟩ :=
    Sec.smul_apply _ _ _
  refine h1.trans ?_
  rw [map_pow, hN i]
  rfl

end QC
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

section Surj

variable {p G}

theorem tmap_congr {c₁ c₂ : Chart p} (h₁ h₂ : c₁ ≤ c₂) (t : T p G c₂) : tmap (G := G) h₁ t = tmap h₂ t := rfl

theorem tmap_comp {c₁ c₂ c₃ : Chart p} (h₁ : c₁ ≤ c₂) (h₂ : c₂ ≤ c₃) (h₃ : c₁ ≤ c₃) (t : T p G c₃) :
    tmap (G := G) h₃ t = tmap h₁ (tmap h₂ t) := (tmap_tmap h₁ h₂ t).symm

theorem cut_mono {c₁ c₂ : Chart p} (h : c₁ ≤ c₂) {W : V'.Opens} (h₁ : c₁.V.1 ≤ W) (h₂ : c₂.V.1 ≤ W) (f : Γ(V', W)) :
    cut c₁ h₁ f ≤ cut c₂ h₂ f := by
  refine ⟨h.1, ?_⟩
  show (cut c₁ h₁ f).V.1 ≤ (cut c₂ h₂ f).V.1
  rw [cut_V, cut_V]
  exact inf_le_inf_right _ h.2

theorem tmap_cut_sub_eq_zero (V : V'.affineOpens) (f : Γ(V', V.1)) (x : Sec p G (V'.basicOpen f)) (N : ℕ)
    (ci cj e : Chart p) (hci : ci.V.1 ≤ V.1) (hcj : cj.V.1 ≤ V.1) (hei : e ≤ ci) (hej : e ≤ cj)
    (ti : T p G ci) (tj : T p G cj)
    (hti : tmap (cut_le ci hci f) ti = rV ((cut_le ci hci f).2.trans hci) (f ^ N) • x.1 ⟨cut ci hci f, cut_V_le ci hci f⟩)
    (htj : tmap (cut_le cj hcj f) tj = rV ((cut_le cj hcj f).2.trans hcj) (f ^ N) • x.1 ⟨cut cj hcj f, cut_V_le cj hcj f⟩) :
    tmap (cut_le e (hei.2.trans hci) f) (tmap hei ti - tmap hej tj) = 0 := by
  have heV : e.V.1 ≤ V.1 := hei.2.trans hci
  have key : ∀ (c : Chart p) (hc : c.V.1 ≤ V.1) (hec : e ≤ c) (t : T p G c)
      (ht : tmap (cut_le c hc f) t = rV ((cut_le c hc f).2.trans hc) (f ^ N) • x.1 ⟨cut c hc f, cut_V_le c hc f⟩),
      tmap (cut_le e heV f) (tmap hec t) = rV ((cut_le e heV f).2.trans heV) (f ^ N) • x.1 ⟨cut e heV f, cut_V_le e heV f⟩ := by
    intro c hc hec t ht
    have hcc : cut e heV f ≤ cut c hc f := cut_mono hec heV hc f
    rw [tmap_tmap, tmap_comp hcc (cut_le c hc f), ht, tmap_smul, rV_rV,
      Sec.compat x ⟨cut e heV f, cut_V_le e heV f⟩ ⟨cut c hc f, cut_V_le c hc f⟩ hcc]
  rw [map_sub, key ci hci hei ti hti, key cj hcj hej tj htj, sub_self]

theorem lift_mono (V : V'.affineOpens) (f : Γ(V', V.1)) (c : Chart p) (hc : c.V.1 ≤ V.1)
    (x : T p G (cut c hc f)) {m n : ℕ} (hmn : m ≤ n)
    (h : ∃ t : T p G c, tmap (cut_le c hc f) t = rV ((cut_le c hc f).2.trans hc) (f ^ m) • x) :
    ∃ t : T p G c, tmap (cut_le c hc f) t = rV ((cut_le c hc f).2.trans hc) (f ^ n) • x := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨rV hc (f ^ k) • t, ?_⟩
  rw [tmap_smul, ht, rV_rV, ← mul_smul, ← map_mul, ← pow_add, add_comm]

theorem exists_res_eq_pow_smul (hq : G.IsQuasicoherent) (V : V'.affineOpens) (f : Γ(V', V.1))
    (x : (pullbackDatum p G).obj (V'.basicOpen f)) :
    ∃ (n : ℕ) (y : (pullbackDatum p G).obj V.1),
      (pullbackDatum p G).res (V'.basicOpen_le f) y = rV (V'.basicOpen_le f) (f ^ n) • x := by
  classical
  obtain ⟨ι, hι, g, U, hspan, hgU⟩ := exists_finite_chartBasic_cover p V
  let c : ι → Chart p := fun i => bchart (U i) V (g i) (hgU i)
  have hcV : ∀ i, (c i).V.1 ≤ V.1 := fun i => V'.basicOpen_le (g i)
  have hcovV : V.1 ≤ ⨆ i, (c i).V.1 := le_iSup_basicOpen_of_span_eq_top V g hspan
  let c' : ι → Chart p := fun i => cut (c i) (hcV i) f
  have hc'D : ∀ i, (c' i).V.1 ≤ V'.basicOpen f := fun i => cut_V_le _ _ _
  have hcovD : V'.basicOpen f ≤ ⨆ i, (c' i).V.1 := by
    intro z hz
    have hzV : z ∈ V.1 := V'.basicOpen_le f hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcovV hzV)
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    show z ∈ (c' i).V.1
    rw [show (c' i).V.1 = (c i).V.1 ⊓ V'.basicOpen f from cut_V _ _ _]
    exact ⟨hi, hz⟩

  have hA : ∀ i, ∃ (n : ℕ) (t : T p G (c i)),
      tmap (cut_le (c i) (hcV i) f) t = rV ((cut_le (c i) (hcV i) f).2.trans (hcV i)) (f ^ n) • x.1 ⟨c' i, hc'D i⟩ :=
    fun i => exists_tmap_cut_eq_pow_smul hq (c i) (hcV i) f (x.1 ⟨c' i, hc'D i⟩)
  obtain ⟨N, hN⟩ := exists_forall_ge_of_finite
    (P := fun i n => ∃ t : T p G (c i),
      tmap (cut_le (c i) (hcV i) f) t = rV ((cut_le (c i) (hcV i) f).2.trans (hcV i)) (f ^ n) • x.1 ⟨c' i, hc'D i⟩)
    (fun i m n hmn h => lift_mono V f (c i) (hcV i) _ hmn h) hA
  choose t ht using hN

  let W : ι × ι → V'.affineOpens := fun ij => ⟨V'.basicOpen (g ij.1 * g ij.2), V.2.basicOpen _⟩
  have hW : ∀ ij, (W ij).1 = (c ij.1).V.1 ⊓ (c ij.2).V.1 := fun ij => Scheme.basicOpen_mul _ _ _
  have hWO : ∀ ij, (W ij).1 ≤ p ⁻¹ᵁ ((U ij.1).1 ⊓ (U ij.2).1) := by
    intro ij z hz
    rw [hW] at hz
    exact ⟨hgU ij.1 hz.1, hgU ij.2 hz.2⟩
  choose κ hκ h Uo hspan' hD hUo using fun ij : ι × ι => exists_finite_chartBasic_cover_le p (W ij) _ (hWO ij)
  haveI : ∀ ij, Fintype (κ ij) := hκ
  let e : ∀ ij : ι × ι, κ ij → Chart p := fun ij k => bchart (Uo ij k) (W ij) (h ij k) (hD ij k)
  have heW : ∀ ij k, (e ij k).V.1 ≤ (W ij).1 := fun ij k => V'.basicOpen_le _
  have he₁ : ∀ ij k, e ij k ≤ c ij.1 := fun ij k =>
    ⟨(hUo ij k).trans inf_le_left, (heW ij k).trans ((hW ij).le.trans inf_le_left)⟩
  have he₂ : ∀ ij k, e ij k ≤ c ij.2 := fun ij k =>
    ⟨(hUo ij k).trans inf_le_right, (heW ij k).trans ((hW ij).le.trans inf_le_right)⟩
  have heV : ∀ ij k, (e ij k).V.1 ≤ V.1 := fun ij k => (he₁ ij k).2.trans (hcV ij.1)

  let Δ : ∀ (ij : ι × ι) (k : κ ij), T p G (e ij k) := fun ij k => tmap (he₁ ij k) (t ij.1) - tmap (he₂ ij k) (t ij.2)
  have hΔ : ∀ (s : Σ ij, κ ij), ∃ m : ℕ, (rV (heV s.1 s.2) f) ^ m • Δ s.1 s.2 = 0 := fun s =>
    exists_pow_smul_eq_zero_of_tmap_cut_eq_zero hq (e s.1 s.2) (heV s.1 s.2) f _
      (tmap_cut_sub_eq_zero V f x N (c s.1.1) (c s.1.2) (e s.1 s.2) (hcV s.1.1) (hcV s.1.2) (he₁ s.1 s.2) (he₂ s.1 s.2)
        (t s.1.1) (t s.1.2) (ht s.1.1) (ht s.1.2))
  obtain ⟨K, hK⟩ := exists_forall_ge_of_finite (P := fun (s : Σ ij, κ ij) m => (rV (heV s.1 s.2) f) ^ m • Δ s.1 s.2 = 0)
    (fun s m n hmn hh => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [add_comm, pow_add, mul_smul, hh, smul_zero]) hΔ

  let Tval : ∀ i, T p G (c i) := fun i => rV (hcV i) (f ^ K) • t i
  have hcompat : ∀ (i j : ι) (d : Chart p) (hi : d ≤ c i) (hj : d ≤ c j), tmap hi (Tval i) = tmap hj (Tval j) := by
    intro i j d hi hj
    have hdW : d.V.1 ≤ (W (i, j)).1 := by rw [hW]; exact le_inf hi.2 hj.2

    let Dk : κ (i, j) → V'.affineOpens := fun k => ⟨V'.basicOpen (rV hdW (h (i, j) k)), d.V.2.basicOpen _⟩
    have hDk : ∀ k, (Dk k).1 = d.V.1 ⊓ V'.basicOpen (h (i, j) k) := fun k => Scheme.basicOpen_res _ _ _
    have hDkO : ∀ k, (Dk k).1 ≤ p ⁻¹ᵁ (d.U.1 ⊓ (Uo (i, j) k).1) := by
      intro k z hz
      rw [hDk] at hz
      exact ⟨d.le hz.1, hD (i, j) k hz.2⟩
    choose μ hμ hh UU hspan'' hDD hUU using fun k => exists_finite_chartBasic_cover_le p (Dk k) _ (hDkO k)
    let ee : (Σ k, μ k) → Chart p := fun s => bchart (UU s.1 s.2) (Dk s.1) (hh s.1 s.2) (hDD s.1 s.2)
    have hee_d : ∀ s, ee s ≤ d := fun s =>
      ⟨(hUU s.1 s.2).trans inf_le_left, (V'.basicOpen_le _).trans ((hDk s.1).le.trans inf_le_left)⟩
    have hee_e : ∀ s, ee s ≤ e (i, j) s.1 := fun s =>
      ⟨(hUU s.1 s.2).trans inf_le_right, by
        refine (V'.basicOpen_le _).trans ((hDk s.1).le.trans (inf_le_right.trans ?_))
        exact le_rfl⟩
    have hcov : d.V.1 ≤ ⨆ s, (ee s).V.1 := by
      intro z hz
      have hz' : z ∈ (W (i, j)).1 := hdW hz
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (le_iSup_basicOpen_of_span_eq_top (W (i, j)) (h (i, j)) (hspan' (i, j)) hz')
      have hzD : z ∈ (Dk k).1 := by rw [hDk]; exact ⟨hz, hk⟩
      obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (le_iSup_basicOpen_of_span_eq_top (Dk k) (hh k) (hspan'' k) hzD)
      exact Opens.mem_iSup.mpr ⟨⟨k, l⟩, hl⟩
    apply T_ext_of_cover hq d ee hee_d hcov
    intro s
    have hi' : ee s ≤ c i := Chart.le_trans' (hee_d s) hi
    have hj' : ee s ≤ c j := Chart.le_trans' (hee_d s) hj
    rw [tmap_tmap, tmap_tmap, ← sub_eq_zero]
    show tmap hi' (Tval i) - tmap hj' (Tval j) = 0
    simp only [Tval]
    rw [tmap_smul, tmap_smul, rV_rV, rV_rV, tmap_comp (hee_e s) (he₁ (i, j) s.1) hi', tmap_comp (hee_e s) (he₂ (i, j) s.1) hj',
      ← rV_rV (hee_e s).2 (heV (i, j) s.1)]
    have hK' := congrArg (tmap (hee_e s)) (hK ⟨(i, j), s.1⟩)
    rw [map_zero, ← map_pow, tmap_smul, map_sub, smul_sub] at hK'
    exact hK'

  obtain ⟨y, hy⟩ := Sec.exists_of_cover hq c hcV hcovV Tval hcompat
  refine ⟨K + N, y, Sec.ext_of_cover hq _ _ c' hc'D hcovD fun i => ?_⟩
  have hL : ((pullbackDatum p G).res (V'.basicOpen_le f) y).1 ⟨c' i, hc'D i⟩ =
      rV ((cut_le (c i) (hcV i) f).2.trans (hcV i)) (f ^ (K + N)) • x.1 ⟨c' i, hc'D i⟩ := by
    rw [pullbackDatum_res_apply]
    show y.1 ⟨c' i, (cut_le (c i) (hcV i) f).2.trans (hcV i)⟩ = _
    rw [← Sec.compat y ⟨c' i, _⟩ ⟨c i, hcV i⟩ (cut_le (c i) (hcV i) f), hy i]
    show tmap (cut_le (c i) (hcV i) f) (rV (hcV i) (f ^ K) • t i) = _
    rw [tmap_smul, ht i, rV_rV, ← mul_smul, ← map_mul, ← pow_add]
  have hR : ((rV (V'.basicOpen_le f) (f ^ (K + N)) • x : Sec p G (V'.basicOpen f))).1 ⟨c' i, hc'D i⟩ =
      rV ((cut_le (c i) (hcV i) f).2.trans (hcV i)) (f ^ (K + N)) • x.1 ⟨c' i, hc'D i⟩ :=
    (Sec.smul_apply (rV (V'.basicOpen_le f) (f ^ (K + N))) x ⟨c' i, hc'D i⟩).trans (by rw [rV_rV])
  exact hL.trans hR.symm

theorem isQuasicoherent (hq : G.IsQuasicoherent) : (pullbackDatum p G).IsQuasicoherent := by
  intro V f
  exact ⟨fun x => exists_res_eq_pow_smul hq V f x, fun y hy => exists_pow_smul_eq_zero hq V f y hy⟩

end Surj
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

end P1Sol.Big
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Chart P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol.Fam P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom.P1Sol"

theorem solution
    {A : Type u} [CommRing A]
    {P V' : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) (p : V' ⟶ P)
    (G : OModulePresheaf q) (hq : G.IsQuasicoherent) :
    ∃ (G' : OModulePresheaf (p ≫ q))
      (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (G.obj U.1 →ₗ[A] G'.obj V.1)),
      G'.IsQuasicoherent ∧ (G.IsCoherent → G'.IsCoherent) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : G.obj U.1),
        η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x) ∧

      (∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
        (hV : V₁.1 ≤ V₂.1) (x : G.obj U.1), G'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x) ∧

      (∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
        (hU : U₁.1 ≤ U₂.1) (x : G.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (G.res hU x)) ∧

      (∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1),
        letI := (p.appLE U.1 V.1 h).hom.toAlgebra
        ∃ β : Γ(V', V.1) ⊗[Γ(P, U.1)] G.obj U.1 ≃ₗ[Γ(V', V.1)] G'.obj V.1,
          ∀ x : G.obj U.1, β (1 ⊗ₜ x) = η U V h x) ∧

      (∀ (W : P.affineOpens) (W' : V'.affineOpens) (hW : W'.1 = p ⁻¹ᵁ W.1),
        IsIso (p ∣_ W.1) → Function.Bijective (η W W' hW.le)) := by
  refine ⟨P1Sol.pullbackDatum p G, P1Sol.eta hq, P1Sol.Big.isQuasicoherent hq,
    fun hG => P1Sol.Big.isCoherent p G hq (P1Sol.Big.isQuasicoherent hq) hG,
    P1Sol.Big.eta_smul p G hq, P1Sol.Big.eta_res p G hq, P1Sol.Big.eta_resU p G hq,
    P1Sol.Big.exists_beta p G hq, P1Sol.Big.eta_bijective p G hq⟩

end S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_isQuasicoherent_forall_exists_linearEquiv_tensorProduct_of_hom (solution)
