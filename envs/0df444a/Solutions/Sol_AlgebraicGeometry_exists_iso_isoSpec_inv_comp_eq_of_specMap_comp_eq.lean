-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/da82f9d8-3314-5d32-85f2-37bc050d7bbd

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace ISOAux

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

theorem bijective_of_sub_mem_of_fix {C : Type u} [CommRing C] (J : Ideal C)
    (ψ : C →+* C) (hmod : ∀ c, ψ c - c ∈ J) (hfix : ∀ c ∈ J, ψ c = c) : Function.Bijective ψ := by
  constructor
  · intro a b hab
    have h1 : ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ∈ J := by have := hmod (a - b); rwa [h1, zero_sub, neg_mem_iff] at this
    have h3 := hfix _ h2
    rw [h1] at h3
    exact sub_eq_zero.mp h3.symm
  · intro c
    refine ⟨c - (ψ c - c), ?_⟩
    rw [map_sub, hfix _ (hmod c)]; abel

end ISOAux

theorem solution
    {B B₁ : Type u} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hI2 : RingHom.ker (algebraMap B B₁) * RingHom.ker (algebraMap B B₁) = ⊥)
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₁ : X₁ ⟶ Spec (CommRingCat.of B₁)) (g : X₁ ⟶ X)
    (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (U : X.Opens) (hU : IsAffineOpen U)
    (v : Spec (CommRingCat.of Γ(X, U)) ⟶ X)
    (hv : letI := algebraOfHom f U
      v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))))
    (hvu : letI := algebraOfHom f U
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ v) :
    ∃ α : (U : Scheme.{u}) ≅ U,
      hU.isoSpec.inv ≫ α.hom ≫ U.ι = v ∧
      α.hom ≫ U.ι ≫ f = U.ι ≫ f ∧
      (g ∣_ U) ≫ α.hom = g ∣_ U := by
  letI instA : Algebra B Γ(X, U) := algebraOfHom f U
  classical
  have hJJ : (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) * (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) = ⊥ := by
    rw [← Ideal.map_mul, hI2, Ideal.map_bot]

  have hrange : Set.range v.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have hJp : (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) ≤ p.asIdeal := by
      intro j hj
      have h2 : j * j ∈ (⊥ : Ideal Γ(X, U)) := hJJ ▸ Ideal.mul_mem_mul hj hj
      rw [Ideal.mem_bot] at h2
      exact (p.2.mem_or_mem (by rw [h2]; exact p.asIdeal.zero_mem)).elim id id
    have hker : RingHom.ker (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))) ≤ p.asIdeal := by
      rw [Ideal.mk_ker]; exact hJp
    haveI : p.asIdeal.IsPrime := p.2
    let q : Spec (CommRingCat.of (Γ(X, U) ⧸ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))) :=
      ⟨p.asIdeal.map (Ideal.Quotient.mk _), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
    have hq : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))))).base q = p := by
      apply PrimeSpectrum.ext
      show Ideal.comap (Ideal.Quotient.mk _) (p.asIdeal.map (Ideal.Quotient.mk _)) = p.asIdeal
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hJp
    have e := congrArg (fun h => h.base q) hvu
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
    rw [hq] at e
    rw [← e, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  let α' : Spec (CommRingCat.of Γ(X, U)) ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι v hrange
  have hα' : α' ≫ U.ι = v := IsOpenImmersion.lift_fac U.ι v hrange

  let ψh : Γ(X, U) ⟶ Γ(X, U) := U.topIso.inv ≫ α'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom
  have hαψ : α' ≫ U.toSpecΓ = Spec.map ψh := ISOAux.comp_toSpecΓ U α'
  haveI : IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have h2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ α' =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.isoSpec.inv := by
    rw [← cancel_mono U.ι, Category.assoc, hα', Category.assoc, hU.isoSpec_inv_ι]
    exact hvu.symm
  have hψmk : ψh ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))) =
      CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hαψ, ← Category.assoc, h2, Category.assoc, hU.isoSpec_inv_toSpecΓ]
    exact Category.comp_id _
  have hmod : ∀ c, ψh.hom c - c ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) := by
    intro c
    rw [← Ideal.Quotient.eq, eq_comm]
    have := congrArg (fun φ => CommRingCat.Hom.hom φ c) hψmk
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using this.symm

  have hover : (α' ≫ U.ι) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by rw [hα']; exact hv
  have hψB : ∀ r : B, ψh.hom (algebraMap B Γ(X, U) r) = algebraMap B Γ(X, U) r :=
    fun r => ISOAux.chart_algebraMap_of_over f U α' (algebraMap B Γ(X, U)) hover r

  have hfix : ∀ c ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)), ψh.hom c = c := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hψB i
    | zero => exact map_zero _
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
    | smul a x hx ihx =>
      rw [smul_eq_mul, map_mul, ihx]
      have hd : ψh.hom a - a ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) := hmod a
      have hz : (ψh.hom a - a) * x = 0 := by
        have hx' : x ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)) := hx
        have := Ideal.mul_mem_mul hd hx'
        rwa [hJJ, Ideal.mem_bot] at this
      rw [sub_mul, sub_eq_zero] at hz
      rw [hz]
  have hbij : Function.Bijective ψh.hom := ISOAux.bijective_of_sub_mem_of_fix _ ψh.hom hmod hfix
  haveI : IsIso ψh := (ConcreteCategory.isIso_iff_bijective ψh).mpr hbij
  haveI : IsIso α' := IsIso.of_isIso_fac_right hαψ

  refine ⟨asIso (hU.isoSpec.hom ≫ α'), ?_, ?_, ?_⟩
  · rw [asIso_hom]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; exact hα'
  · rw [asIso_hom]
    have h3 : α' ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))) := by rw [← Category.assoc]; exact hover
    simp only [Category.assoc]
    rw [h3]
    symm
    rw [← Iso.inv_comp_eq, ← Category.assoc]
    apply ISOAux.over_of_chart_algebraMap f U hU.isoSpec.inv (algebraMap B Γ(X, U))
    intro r
    have hid : U.topIso.inv ≫ hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).hom = 𝟙 _ := by
      apply Spec.map_injective
      have hc := ISOAux.comp_toSpecΓ (R := CommRingCat.of Γ(X, U)) U hU.isoSpec.inv
      rw [Spec.map_id, ← hc]
      exact hU.isoSpec_inv_toSpecΓ
    rw [hid]; rfl
  ·
    rw [asIso_hom]
    have hnat := Scheme.Opens.toSpecΓ_naturality g U

    have hkill : ∀ c ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)), (g.app U).hom c = 0 := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        rw [algebraMap_algebraOfHom]

        have s1 : (g.app U).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom i)) =
            (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ g.app U).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom i)) := rfl
        rw [s1, g.naturality]
        show (X₁.presheaf.map _).hom ((g.app ⊤).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom i))) = 0
        have s2 : (g.app ⊤).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom i)) =
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (g ≫ f).appTop).hom i := by
          rw [Scheme.Hom.comp_appTop]; rfl
        rw [s2, hg.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
        show (X₁.presheaf.map _).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom (algebraMap B B₁ i))) = 0
        rw [RingHom.mem_ker.mp hi, map_zero, map_zero, map_zero]
      | zero => exact map_zero _
      | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
      | smul a x hx ihx => rw [smul_eq_mul, map_mul, ihx, mul_zero]
    let ℓ : (Γ(X, U) ⧸ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))) →+* Γ(X₁, g ⁻¹ᵁ U) :=
      Ideal.Quotient.lift _ (g.app U).hom hkill
    have hfac : g.app U = CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U)))) ≫ CommRingCat.ofHom ℓ :=
      CommRingCat.hom_ext (RingHom.ext fun c => rfl)
    calc (g ∣_ U) ≫ hU.isoSpec.hom ≫ α' = ((g ∣_ U) ≫ U.toSpecΓ) ≫ α' := by rw [hU.isoSpec_hom, Category.assoc]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (g.app U) ≫ α' := by rw [← hnat, Category.assoc]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ α' := by
          rw [hfac, Spec.map_comp, Category.assoc]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.isoSpec.inv := by
          rw [h2]
      _ = (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (g.app U) ≫ hU.isoSpec.inv := by rw [hfac, Spec.map_comp, Category.assoc]
      _ = ((g ∣_ U) ≫ U.toSpecΓ) ≫ hU.isoSpec.inv := by rw [← hnat, Category.assoc]
      _ = g ∣_ U := by rw [← hU.isoSpec_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq (solution)
