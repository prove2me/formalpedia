-- Prove2me | solution 1 for AlgebraicGeometry.bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/08aff6e3-b3b3-5220-8a22-620b66f984de

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_of_etale_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option maxHeartbeats 3200000

noncomputable section

namespace TubeBij

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem residue_base_apply {A : Type u} [CommRing A] [IsLocalRing A] (z : ↥(Spec (CommRingCat.of (ResidueField A)))) :
    (Spec.map (CommRingCat.ofHom (residue A))).base z = closedPoint A := by
  have hz : z = closedPoint (ResidueField A) := Subsingleton.elim _ _
  subst hz
  exact IsLocalRing.comap_closedPoint (residue A)

theorem eq_top_of_closedPoint_mem {A : Type u} [CommRing A] [IsLocalRing A] (W : (Spec (CommRingCat.of A)).Opens)
    (h : closedPoint A ∈ W) : W = ⊤ :=
  (IsLocalRing.closed_point_mem_iff).mp h

theorem exists_point_over {A : Type u} [CommRing A] [IsLocalRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (hres : IsIso (g.residueFieldMap x))
    (t : Spec (CommRingCat.of A) ⟶ Y) (htx : t.base (closedPoint A) = g.base x) :
    ∃ e₀ : Spec (CommRingCat.of (ResidueField A)) ⟶ X,
      e₀ ≫ g = Spec.map (CommRingCat.ofHom (residue A)) ≫ t ∧ ∀ z, e₀.base z = x := by
  classical
  set r := Spec.map (CommRingCat.ofHom (residue A)) with hr

  set P := (Scheme.SpecToEquivOfField (ResidueField A) Y) (r ≫ t) with hP
  have hP1 : P.1 = g.base x := by
    show (r ≫ t).base (closedPoint (ResidueField A)) = g.base x
    rw [Scheme.Hom.comp_apply, hr, residue_base_apply, htx]
  have hsymm : Spec.map P.2 ≫ Y.fromSpecResidueField P.1 = r ≫ t :=
    (Scheme.SpecToEquivOfField (ResidueField A) Y).symm_apply_apply (r ≫ t)

  let ψ : Y.residueField (g.base x) ⟶ CommRingCat.of (ResidueField A) := (Y.residueFieldCongr hP1.symm).hom ≫ P.2
  haveI := hres
  let φ : X.residueField x ⟶ CommRingCat.of (ResidueField A) := inv (g.residueFieldMap x) ≫ ψ
  refine ⟨Spec.map φ ≫ X.fromSpecResidueField x, ?_, fun z => ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp]
    have hc : g.residueFieldMap x ≫ φ = ψ := by
      simp only [φ, IsIso.hom_inv_id_assoc]
    rw [hc]
    show Spec.map ((Y.residueFieldCongr hP1.symm).hom ≫ P.2) ≫ Y.fromSpecResidueField (g.base x) = r ≫ t
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact hsymm
  · rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem exists_section {A : Type u} [CommRing A] [HenselianLocalRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (U : X.Opens) (hxU : x ∈ U) [Etale (U.ι ≫ g)] (hres : IsIso (g.residueFieldMap x))
    (t : Spec (CommRingCat.of A) ⟶ Y) (htx : t.base (closedPoint A) = g.base x) :
    ∃ s : Spec (CommRingCat.of A) ⟶ X, s ≫ g = t ∧ s.base (closedPoint A) = x := by
  classical
  obtain ⟨e₀, he₀, he₀x⟩ := exists_point_over g x hres t htx

  have hrange : Set.range e₀.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [he₀x z, Scheme.Opens.range_ι]
    exact hxU
  let e₀U : Spec (CommRingCat.of (ResidueField A)) ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι e₀ hrange
  have he₀U : e₀U ≫ U.ι = e₀ := IsOpenImmersion.lift_fac U.ι e₀ hrange

  let eU : Spec (CommRingCat.of (ResidueField A)) ⟶ pullback (U.ι ≫ g) t :=
    pullback.lift e₀U (Spec.map (CommRingCat.ofHom (residue A))) (by rw [← Category.assoc, he₀U, he₀])
  obtain ⟨s', hs'q, hs'e⟩ :=
    AlgebraicGeometry.exists_section_comp_eq_of_etale_of_henselianLocalRing (pullback.snd (U.ι ≫ g) t) eU
      (pullback.lift_snd _ _ _)
  refine ⟨s' ≫ pullback.fst (U.ι ≫ g) t ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, hs'q, Category.id_comp]
  · have h1 : (Spec.map (CommRingCat.ofHom (residue A)) ≫ s' ≫ pullback.fst (U.ι ≫ g) t ≫ U.ι).base
        (closedPoint (ResidueField A)) = x := by
      rw [← Category.assoc, hs'e, ← Category.assoc, pullback.lift_fst, he₀U, he₀x]
    rwa [Scheme.Hom.comp_apply, residue_base_apply] at h1

theorem pullback_point_eq_of_isIso_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S) (x₀ : X) [IsIso (f.residueFieldMap x₀)]
    (P Q : ↥(pullback f f)) (hP₁ : pullback.fst f f P = x₀) (hP₂ : pullback.snd f f P = x₀)
    (hQ₁ : pullback.fst f f Q = x₀) (hQ₂ : pullback.snd f f Q = x₀) : P = Q := by
  classical
  apply Scheme.Pullback.carrierEquiv.injective
  rw [Scheme.Pullback.carrierEquiv_eq_iff]
  have hT : (Scheme.Pullback.carrierEquiv P).1 = (Scheme.Pullback.carrierEquiv Q).1 := by
    apply Scheme.Pullback.Triplet.ext
    · show pullback.fst f f P = pullback.fst f f Q
      rw [hP₁, hQ₁]
    · show pullback.snd f f P = pullback.snd f f Q
      rw [hP₂, hQ₂]
  refine ⟨hT, ?_⟩

  set TQ := (Scheme.Pullback.carrierEquiv Q).1 with hTQ
  have hTx : TQ.x = x₀ := hQ₁
  have hiso : ∀ (y : X) (_ : y = x₀), IsIso (f.residueFieldMap y) := by
    rintro _ rfl
    infer_instance
  haveI := hiso TQ.x hTx
  haveI : IsIso ((S.residueFieldCongr TQ.hx).inv ≫ f.residueFieldMap TQ.x) := inferInstance
  haveI : IsIso (Scheme.Pullback.Triplet.tensorInr TQ) := by
    unfold Scheme.Pullback.Triplet.tensorInr Scheme.Pullback.Triplet.tensor
    infer_instance
  haveI : Subsingleton ↥(Spec TQ.tensor) := by
    have e : Spec TQ.tensor ≅ Spec (X.residueField TQ.y) := Scheme.Spec.mapIso (asIso (Scheme.Pullback.Triplet.tensorInr TQ)).op
    exact (Scheme.homeoOfIso e).toEquiv.subsingleton
  exact Subsingleton.elim _ _

theorem section_ext {A : Type u} [CommRing A] [IsLocalRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (U : X.Opens) (hxU : x ∈ U) [FormallyUnramified (U.ι ≫ g)] [LocallyOfFiniteType (U.ι ≫ g)]
    (hres : IsIso (g.residueFieldMap x))
    (s₁ s₂ : Spec (CommRingCat.of A) ⟶ X) (h₁ : s₁.base (closedPoint A) = x) (h₂ : s₂.base (closedPoint A) = x)
    (hg : s₁ ≫ g = s₂ ≫ g) : s₁ = s₂ := by
  classical

  have hfac : ∀ s : Spec (CommRingCat.of A) ⟶ X, s.base (closedPoint A) = x → Set.range s.base ⊆ Set.range U.ι.base := by
    intro s hs
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have htop : s ⁻¹ᵁ U = ⊤ := eq_top_of_closedPoint_mem _ (show s.base (closedPoint A) ∈ U by rw [hs]; exact hxU)
    have hz : z ∈ s ⁻¹ᵁ U := by rw [htop]; trivial
    exact hz
  let s₁' := IsOpenImmersion.lift U.ι s₁ (hfac s₁ h₁)
  let s₂' := IsOpenImmersion.lift U.ι s₂ (hfac s₂ h₂)
  have hs₁ : s₁' ≫ U.ι = s₁ := IsOpenImmersion.lift_fac _ _ _
  have hs₂ : s₂' ≫ U.ι = s₂ := IsOpenImmersion.lift_fac _ _ _
  have hg' : s₁' ≫ (U.ι ≫ g) = s₂' ≫ (U.ι ≫ g) := by
    rw [← Category.assoc, hs₁, ← Category.assoc, hs₂, hg]

  have hx₁ : U.ι.base (s₁'.base (closedPoint A)) = x := by rw [← Scheme.Hom.comp_apply, hs₁, h₁]
  have hx₂ : U.ι.base (s₂'.base (closedPoint A)) = x := by rw [← Scheme.Hom.comp_apply, hs₂, h₂]
  have hx₁₂ : s₁'.base (closedPoint A) = s₂'.base (closedPoint A) :=
    U.ι.isOpenEmbedding.injective (hx₁.trans hx₂.symm)

  set d := pullback.lift s₁' s₂' hg' with hd
  have hiso : ∀ (y : X) (_ : y = x), IsIso (g.residueFieldMap y) := by
    rintro _ rfl
    exact hres
  haveI h1 : IsIso (g.residueFieldMap (U.ι.base (s₁'.base (closedPoint A)))) := hiso _ hx₁
  haveI h2 : IsIso (U.ι.residueFieldMap (s₁'.base (closedPoint A))) := inferInstance
  haveI : IsIso ((U.ι ≫ g).residueFieldMap (s₁'.base (closedPoint A))) := by
    rw [Scheme.residueFieldMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  have hmem : d.base (closedPoint A) ∈ Set.range (pullback.diagonal (U.ι ≫ g)).base := by
    refine ⟨s₁'.base (closedPoint A), ?_⟩
    apply pullback_point_eq_of_isIso_residueFieldMap (U.ι ≫ g) (s₁'.base (closedPoint A))
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
    · rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
    · rw [← Scheme.Hom.comp_apply, hd, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, hd, pullback.lift_snd, hx₁₂]
  have hrange : Set.range d.base ⊆ Set.range (pullback.diagonal (U.ι ≫ g)).base := by
    rintro _ ⟨z, rfl⟩
    have htop : d ⁻¹ᵁ (pullback.diagonal (U.ι ≫ g)).opensRange = ⊤ := eq_top_of_closedPoint_mem _ hmem
    have hz : z ∈ d ⁻¹ᵁ (pullback.diagonal (U.ι ≫ g)).opensRange := by rw [htop]; trivial
    exact hz
  let ℓ := IsOpenImmersion.lift (pullback.diagonal (U.ι ≫ g)) d hrange
  have hℓ : ℓ ≫ pullback.diagonal (U.ι ≫ g) = d := IsOpenImmersion.lift_fac _ _ _
  have h12 : s₁' = s₂' := by
    calc s₁' = d ≫ pullback.fst _ _ := by rw [hd, pullback.lift_fst]
      _ = ℓ := by rw [← hℓ, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      _ = d ≫ pullback.snd _ _ := by rw [← hℓ, Category.assoc, pullback.diagonal_snd, Category.comp_id]
      _ = s₂' := by rw [hd, pullback.lift_snd]
  rw [← hs₁, ← hs₂, h12]

end TubeBij

end

open TubeBij in

theorem solution {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A)) (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : X)
    (U : X.Opens) (hxU : x ∈ U) [Etale (U.ι ≫ g)]
    (hres : IsIso (g.residueFieldMap x)) :
    Function.Bijective (fun s : {s : Spec (CommRingCat.of A) ⟶ X // s ≫ fX = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint A) = x} =>
      (⟨s.1 ≫ g, ⟨by rw [Category.assoc, hg]; exact s.2.1, by rw [Scheme.Hom.comp_apply, s.2.2]⟩⟩ :
        {t : Spec (CommRingCat.of A) ⟶ Y // t ≫ fY = 𝟙 _ ∧ t.base (IsLocalRing.closedPoint A) = g.base x})) := by

  constructor
  · rintro ⟨s₁, hs₁, hs₁x⟩ ⟨s₂, hs₂, hs₂x⟩ h
    have h' : s₁ ≫ g = s₂ ≫ g := congrArg Subtype.val h
    exact Subtype.ext (section_ext g x U hxU hres s₁ s₂ hs₁x hs₂x h')
  · rintro ⟨t, ht, htx⟩
    obtain ⟨s, hsg, hsx⟩ := exists_section g x U hxU hres t htx
    refine ⟨⟨s, ?_, hsx⟩, Subtype.ext hsg⟩
    rw [← hg, ← Category.assoc, hsg, ht]

end S_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap (solution)
