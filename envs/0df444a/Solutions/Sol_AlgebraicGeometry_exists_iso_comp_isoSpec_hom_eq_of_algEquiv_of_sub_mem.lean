-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7b81ce7a-cda2-5b55-ae1f-20dc7cf98c6c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace C4Aux

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem comp_toSpecΓ {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}} (g : Spec R ⟶ (U : Scheme.{u})) :
    g ≫ U.toSpecΓ = Spec.map (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

theorem appLE_topIso_inv {X : Scheme.{u}} (U : X.Opens) {K : CommRingCat.{u}} (c : X ⟶ Spec K) :
    c.appLE ⊤ U le_top ≫ U.topIso.inv = (U.ι ≫ c).appTop := by
  rw [Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.appLE_map]
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop]
  rfl

theorem ext_to_Spec' {R K : CommRingCat.{u}} {f g : Spec R ⟶ Spec K}
    (h : (Scheme.ΓSpecIso K).inv ≫ f.appTop ≫ (Scheme.ΓSpecIso R).hom = (Scheme.ΓSpecIso K).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) :
    f = g := by
  have h' := congrArg (fun q => q ≫ (Scheme.ΓSpecIso R).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact AlgebraicGeometry.ext_to_Spec (by rw [Scheme.Γ_map_op, Scheme.Γ_map_op]; exact h')

variable {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (U : X.Opens)

theorem chart_algebraMap_of_over {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}))
    (F : B →+* R) (hg : (g ≫ U.ι) ≫ f = Spec.map (CommRingCat.ofHom F)) (r : B) :
    letI := algebraOfHom f U
    (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (algebraMap B Γ(X, U) r) = F r := by
  letI := algebraOfHom f U
  rw [algebraMap_algebraOfHom]
  show ((f.appLE ⊤ U le_top ≫ U.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r) = F r
  rw [appLE_topIso_inv, ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc, hg]
  have := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Spec.map (CommRingCat.ofHom F)).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r)) = F r
  rw [← this]
  exact CategoryTheory.Iso.inv_hom_id_apply _ _

theorem over_of_chart_algebraMap {R : Type u} [CommRing R] (g : Spec (CommRingCat.of R) ⟶ (U : Scheme.{u}))
    (F : B →+* R)
    (hg : letI := algebraOfHom f U
      ∀ r : B, (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (algebraMap B Γ(X, U) r) = F r) :
    (g ≫ U.ι) ≫ f = Spec.map (CommRingCat.ofHom F) := by
  letI := algebraOfHom f U
  apply ext_to_Spec'
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  rw [CommRingCat.hom_ofHom, ← hg r, algebraMap_algebraOfHom]
  show _ = ((f.appLE ⊤ U le_top ≫ U.topIso.inv) ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom r)
  rw [appLE_topIso_inv, ← Scheme.Hom.comp_appTop_assoc, Category.assoc g]
  rfl

theorem fromSpec_comp_eq {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by
  letI := algebraOfHom f U
  rw [← hU.isoSpec_inv_ι]
  apply over_of_chart_algebraMap f U hU.isoSpec.inv (algebraMap B Γ(X, U))
  intro r
  have hid : U.topIso.inv ≫ hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom = 𝟙 _ := by
    apply Spec.map_injective
    have hc := comp_toSpecΓ (R := CommRingCat.of Γ(X, U)) U hU.isoSpec.inv
    rw [Spec.map_id, ← hc]
    exact hU.isoSpec_inv_toSpecΓ
  rw [hid]; rfl

end C4Aux

theorem solution
    {B' B₁ : Type u} [CommRing B'] [CommRing B₁] [Algebra B' B₁]
    (hπ : Function.Surjective (algebraMap B' B₁))
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B')) (f₁ : X₁ ⟶ Spec (CommRingCat.of B₁)) (g : X₁ ⟶ X)
    (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B' B₁))))
    (U : X.Opens) (hU : IsAffineOpen U)
    (φ : letI := algebraOfHom f U
      Γ(X, U) ≃ₐ[B'] Γ(X, U))
    (hφ : letI := algebraOfHom f U
      ∀ x : Γ(X, U), φ x - x ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' Γ(X, U))) :
    ∃ α : (U : Scheme.{u}) ≅ U,
      α.hom ≫ hU.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (letI := algebraOfHom f U; φ.toAlgHom.toRingHom)) ∧
      α.hom ≫ U.ι ≫ f = U.ι ≫ f ∧
      (g ∣_ U) ≫ α.hom = g ∣_ U := by
  letI instA : Algebra B' Γ(X, U) := algebraOfHom f U
  classical
  set J : Ideal Γ(X, U) := (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' Γ(X, U)) with hJ
  let φh : CommRingCat.of Γ(X, U) ⟶ CommRingCat.of Γ(X, U) := CommRingCat.ofHom φ.toAlgHom.toRingHom
  haveI : IsIso φh := (ConcreteCategory.isIso_iff_bijective φh).mpr φ.bijective
  haveI : IsIso (Spec.map φh) := inferInstance
  let α : (U : Scheme.{u}) ≅ U := hU.isoSpec ≪≫ asIso (Spec.map φh) ≪≫ hU.isoSpec.symm
  have hα : α.hom = hU.isoSpec.hom ≫ Spec.map φh ≫ hU.isoSpec.inv := by
    simp only [α, Iso.trans_hom, asIso_hom, Iso.symm_hom]
  refine ⟨α, ?_, ?_, ?_⟩
  · rw [hα]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl
  ·
    rw [hα, Category.assoc, Category.assoc, ← Category.assoc hU.isoSpec.inv U.ι f, hU.isoSpec_inv_ι, C4Aux.fromSpec_comp_eq f U hU,
      ← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap B' Γ(X, U)) ≫ φh = CommRingCat.ofHom (algebraMap B' Γ(X, U)) := by
      rw [← CommRingCat.ofHom_comp]; congr 1; exact φ.toAlgHom.comp_algebraMap
    rw [this, ← C4Aux.fromSpec_comp_eq f U hU, ← hU.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  ·
    rw [hα]
    have hnat := Scheme.Opens.toSpecΓ_naturality g U
    have hkill : ∀ c ∈ J, (g.app U).hom c = 0 := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        rw [algebraMap_algebraOfHom]
        have s1 : (g.app U).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) =
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ g.app U).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) := rfl
        rw [s1, g.naturality]
        show (X₁.presheaf.map _).hom ((g.app ⊤).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i))) = 0
        have s2 : (g.app ⊤).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) =
            ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (g ≫ f).appTop).hom i := by
          rw [Scheme.Hom.comp_appTop]; rfl
        rw [s2, hg.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
        show (X₁.presheaf.map _).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom (algebraMap B' B₁ i))) = 0
        rw [RingHom.mem_ker.mp hi, map_zero, map_zero, map_zero]
      | zero => exact map_zero _
      | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
      | smul a x hx ihx => rw [smul_eq_mul, map_mul, ihx, mul_zero]
    let ℓ : (Γ(X, U) ⧸ J) →+* Γ(X₁, g ⁻¹ᵁ U) := Ideal.Quotient.lift _ (g.app U).hom hkill
    have hfac : g.app U = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ℓ :=
      CommRingCat.hom_ext (RingHom.ext fun c => rfl)

    have hφmk : φh ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show Ideal.Quotient.mk J (φ c) = Ideal.Quotient.mk J c
      rw [Ideal.Quotient.eq]
      exact hφ c
    calc (g ∣_ U) ≫ hU.isoSpec.hom ≫ Spec.map φh ≫ hU.isoSpec.inv
        = ((g ∣_ U) ≫ U.toSpecΓ) ≫ Spec.map φh ≫ hU.isoSpec.inv := by rw [hU.isoSpec_hom, Category.assoc]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map φh) ≫
            hU.isoSpec.inv := by rw [← hnat, hfac, Spec.map_comp]; simp only [Category.assoc]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU.isoSpec.inv := by
            rw [← Spec.map_comp, hφmk]
      _ = ((g ∣_ U) ≫ U.toSpecΓ) ≫ hU.isoSpec.inv := by rw [← hnat, hfac, Spec.map_comp]; simp only [Category.assoc]
      _ = g ∣_ U := by rw [← hU.isoSpec_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end S_AlgebraicGeometry_exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem (solution)
