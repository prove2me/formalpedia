-- Prove2me | solution 1 for AlgebraicGeometry.exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4d0bea60-76f7-57e2-b05c-040ed39aa94c

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq
import Theorems.Thm_RingHom_exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing

universe u v

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace ChartPointsAux

theorem isClosedImmersion_and_bijective_specMap_of_surjective_of_nil
    {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Surjective g)
    (hnil : ∀ x, g x = 0 → IsNilpotent x) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) ∧
      Function.Bijective (Spec.map (CommRingCat.ofHom g)).base := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ (by simpa using hg), ?_⟩
  have hb : (⇑(Spec.map (CommRingCat.ofHom g)).base) = PrimeSpectrum.comap g := by
    funext x
    rw [Spec.map_base]
    rfl
  rw [hb]
  refine ⟨PrimeSpectrum.comap_injective_of_surjective g hg, fun 𝔭 => ?_⟩
  have hker : RingHom.ker g ≤ 𝔭.asIdeal := fun x hx =>
    nilpotent_iff_mem_prime.mp (hnil x hx) 𝔭.asIdeal 𝔭.isPrime
  haveI hP : (Ideal.map g 𝔭.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hg hker
  refine ⟨⟨Ideal.map g 𝔭.asIdeal, hP⟩, ?_⟩
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_map_of_surjective g hg, ← RingHom.ker_eq_comap_bot]
  exact sup_eq_left.mpr hker

theorem pullbackRing_prop {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (x : pullbackRing φ' φ'') : φ' x.1.1 = φ'' x.1.2 :=
  x.2

theorem pullbackFst_apply {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (x : pullbackRing φ' φ'') : pullbackFst φ' φ'' x = x.1.1 := rfl

theorem pullbackSnd_apply {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (x : pullbackRing φ' φ'') : pullbackSnd φ' φ'' x = x.1.2 := rfl

end ChartPointsAux

open ChartPointsAux

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in
theorem AlgebraicGeometry.isNilpotent_of_appLE_eq_zero_of_surjective {X Z : Scheme.{0}} (h : Z ⟶ X) [Surjective h]
    (U : X.Opens) (hU : IsAffineOpen U) (V : Z.Opens) (e : V ≤ h ⁻¹ᵁ U) (hV : h ⁻¹ᵁ U ≤ V)
    (a : Γ(X, U)) (ha : h.appLE U V e a = 0) : IsNilpotent a := by
  obtain rfl : V = h ⁻¹ᵁ U := le_antisymm e hV
  rw [← Scheme.Hom.app_eq_appLE] at ha
  have h1 : h ⁻¹ᵁ X.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero]
  have h2 : X.basicOpen a = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨z, rfl⟩ := h.surjective x
    have hz : z ∈ h ⁻¹ᵁ X.basicOpen a := hx
    rw [h1] at hz
    exact hz
  have h3 : PrimeSpectrum.basicOpen a = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    have hx' : x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hx
    rw [h2] at hx'
    exact hx'
  exact (PrimeSpectrum.basicOpen_eq_bot_iff a).mp h3

p2m_open_scoped "AlgebraicGeometry" in
theorem AlgebraicGeometry.isClosedImmersion_and_bijective_specMap_pullbackFst {A' A'' C : Type} [CommRing A'] [CommRing A''] [CommRing C]
    (q' : A' →+* C) (q'' : A'' →+* C) (hq'' : Function.Surjective q'') (hnil : ∀ a, q'' a = 0 → IsNilpotent a) :
    Function.Surjective (pullbackFst q' q'') ∧ (∀ x, pullbackFst q' q'' x = 0 → IsNilpotent x) ∧
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (pullbackFst q' q''))) ∧
    Function.Bijective (Spec.map (CommRingCat.ofHom (pullbackFst q' q''))).base := by
  have hsurj : Function.Surjective (pullbackFst q' q'') := by
    intro a'
    obtain ⟨a'', ha''⟩ := hq'' (q' a')
    exact ⟨⟨(a', a''), show q' a' = q'' a'' from ha''.symm⟩, rfl⟩
  have hnil' : ∀ x, pullbackFst q' q'' x = 0 → IsNilpotent x := by
    intro x hx
    rw [pullbackFst_apply] at hx
    have hx2 : q'' x.1.2 = 0 := by rw [← pullbackRing_prop q' q'' x, hx, map_zero]
    obtain ⟨n, hn⟩ := hnil _ hx2
    refine ⟨n + 1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp [hx]
    · simp [pow_succ, hn]
  exact ⟨hsurj, hnil', isClosedImmersion_and_bijective_specMap_of_surjective_of_nil _ hsurj hnil'⟩

p2m_open_scoped "AlgebraicGeometry" in
theorem AlgebraicGeometry.isClosedImmersion_and_bijective_specMap_pullbackSnd {A' A'' C : Type} [CommRing A'] [CommRing A''] [CommRing C]
    (q' : A' →+* C) (q'' : A'' →+* C) (hq' : Function.Surjective q') (hnil : ∀ a, q' a = 0 → IsNilpotent a) :
    Function.Surjective (pullbackSnd q' q'') ∧ (∀ x, pullbackSnd q' q'' x = 0 → IsNilpotent x) ∧
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (pullbackSnd q' q''))) ∧
    Function.Bijective (Spec.map (CommRingCat.ofHom (pullbackSnd q' q''))).base := by
  have hsurj : Function.Surjective (pullbackSnd q' q'') := by
    intro a''
    obtain ⟨a', ha'⟩ := hq' (q'' a'')
    exact ⟨⟨(a', a''), show q' a' = q'' a'' from ha'⟩, rfl⟩
  have hnil' : ∀ x, pullbackSnd q' q'' x = 0 → IsNilpotent x := by
    intro x hx
    rw [pullbackSnd_apply] at hx
    have hx1 : q' x.1.1 = 0 := by rw [pullbackRing_prop q' q'' x, hx, map_zero]
    obtain ⟨n, hn⟩ := hnil _ hx1
    refine ⟨n + 1, Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp [pow_succ, hn]
    · simp [hx]
  exact ⟨hsurj, hnil', isClosedImmersion_and_bijective_specMap_of_surjective_of_nil _ hsurj hnil'⟩

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry"

namespace B26PL

theorem isIso_snd_chart {W X Y S : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (w : fst ≫ f = snd ≫ g) {U Wc : Scheme.{u}} (j : U ⟶ X) (ιW : Wc ⟶ W) (pc : Wc ⟶ U)
    (sq : IsPullback ιW pc fst j) (H : IsPullback pc (ιW ≫ snd) (j ≫ f) g) :
    IsIso (pullback.snd (pullback.lift fst snd w) (pullback.fst (pullback.fst f g) j)) := by

  set φ := pullback.lift fst snd w with hφ
  set t₁ := pullback.fst (pullback.fst f g) j with ht₁
  set t₂ := pullback.snd (pullback.fst f g) j with ht₂
  have hφ₁ : φ ≫ pullback.fst f g = fst := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd f g = snd := pullback.lift_snd _ _ _
  have ht : t₁ ≫ pullback.fst f g = t₂ ≫ j := pullback.condition

  let σ : pullback (pullback.fst f g) j ⟶ Wc :=
    H.lift t₂ (t₁ ≫ pullback.snd f g) (by rw [← Category.assoc, ← ht, Category.assoc, Category.assoc, pullback.condition])
  have hσ₁ : σ ≫ pc = t₂ := IsPullback.lift_fst _ _ _ _
  have hσ₂ : σ ≫ (ιW ≫ snd) = t₁ ≫ pullback.snd f g := IsPullback.lift_snd _ _ _ _
  have hσφ : (σ ≫ ιW) ≫ φ = t₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hφ₁, sq.w, ← Category.assoc, hσ₁, ht]
    · rw [Category.assoc, Category.assoc, hφ₂, ← Category.assoc σ ιW snd] ; exact hσ₂

  let ψ : pullback (pullback.fst f g) j ⟶ pullback φ t₁ := pullback.lift (σ ≫ ιW) (𝟙 _) (by rw [hσφ, Category.id_comp])
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  ·
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]

      have hc : pullback.fst φ t₁ ≫ fst = (pullback.snd φ t₁ ≫ t₂) ≫ j := by
        rw [← hφ₁, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]
      let τ : pullback φ t₁ ⟶ Wc := sq.lift (pullback.fst φ t₁) (pullback.snd φ t₁ ≫ t₂) hc
      have hτ₁ : τ ≫ ιW = pullback.fst φ t₁ := IsPullback.lift_fst _ _ _ _
      have hτ₂ : τ ≫ pc = pullback.snd φ t₁ ≫ t₂ := IsPullback.lift_snd _ _ _ _
      have hτσ : τ = pullback.snd φ t₁ ≫ σ := by
        apply H.hom_ext
        · rw [hτ₂, Category.assoc, hσ₁]
        · rw [← Category.assoc, hτ₁, Category.assoc, hσ₂, ← hφ₂, ← Category.assoc, pullback.condition, Category.assoc]
      rw [← Category.assoc, ← hτσ, hτ₁]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  ·
    exact pullback.lift_snd _ _ _

end B26PL

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent" namespace IsPullback end AlgebraicGeometry.IsPullback
namespace AlgebraicGeometry.IsPullback
p2m_open_scoped "AlgebraicGeometry" in

private theorem _root_.AlgebraicGeometry.IsPullback.of_openCover_of_isPullback
    {W X Y S : Scheme.{u}} {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (w : fst ≫ f = snd ≫ g) (𝒰 : X.OpenCover)
    {Wc : 𝒰.I₀ → Scheme.{u}} (ιW : ∀ i, Wc i ⟶ W) (pc : ∀ i, Wc i ⟶ 𝒰.X i)
    (sq : ∀ i, IsPullback (ιW i) (pc i) fst (𝒰.f i))
    (H : ∀ i, IsPullback (pc i) (ιW i ≫ snd) (𝒰.f i ≫ f) g) :
    IsPullback fst snd f g := by
  let 𝒱 : (pullback f g).OpenCover := 𝒰.pullback₁ (pullback.fst f g)
  have hiso : IsIso (pullback.lift fst snd w) := by
    rw [← MorphismProperty.isomorphisms.iff]
    exact IsZariskiLocalAtTarget.of_openCover 𝒱 fun i =>
      (MorphismProperty.isomorphisms.iff _).mpr (B26PL.isIso_snd_chart w (𝒰.f i) (ιW i) (pc i) (sq i) (H i))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso (pullback.lift fst snd w)) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.IsPullback
p2m_export "" "AlgebraicGeometry.IsPullback.of_openCover_of_isPullback"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
p2m_open "AlgebraicGeometry"

namespace PushoutLocal

theorem hom_ext_of_forall_openImmersion {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (H : ∀ x : X, ∃ (W : Scheme.{u}) (e : W ⟶ X) (_ : IsOpenImmersion e), x ∈ Set.range ⇑e ∧ e ≫ f = e ≫ g) :
    f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨W, e, he, hx, heq⟩ := H x
  refine ⟨e.opensRange, hx, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp e, Category.assoc, Category.assoc, heq]

theorem range_eq_of_isPullback {P X Y T : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ T} {g : Y ⟶ T}
    (h : IsPullback a b f g) : Set.range ⇑a = ⇑f ⁻¹' Set.range ⇑g := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst]

end PushoutLocal

namespace IsPushout
open PushoutLocal in

private theorem _root_.AlgebraicGeometry.IsPushout.of_openCover_of_isPullback
    {Z X' X'' X : Scheme.{u}} {h' : Z ⟶ X'} {h'' : Z ⟶ X''} {k' : X' ⟶ X} {k'' : X'' ⟶ X}
    (w : h' ≫ k' = h'' ≫ k'') (𝒰 : X.OpenCover)
    (hdir : ∀ (i j : 𝒰.I₀) (x : X), x ∈ (𝒰.f i).opensRange → x ∈ (𝒰.f j).opensRange →
        ∃ l, x ∈ (𝒰.f l).opensRange ∧ (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange)
    {Zc X'c X''c : 𝒰.I₀ → Scheme.{u}}
    (hc' : ∀ i, Zc i ⟶ X'c i) (hc'' : ∀ i, Zc i ⟶ X''c i) (kc' : ∀ i, X'c i ⟶ 𝒰.X i) (kc'' : ∀ i, X''c i ⟶ 𝒰.X i)
    (ιZ : ∀ i, Zc i ⟶ Z) (ι' : ∀ i, X'c i ⟶ X') (ι'' : ∀ i, X''c i ⟶ X'')
    (sq' : ∀ i, IsPullback (ι' i) (kc' i) k' (𝒰.f i))
    (sq'' : ∀ i, IsPullback (ι'' i) (kc'' i) k'' (𝒰.f i))
    (sqZ' : ∀ i, ιZ i ≫ h' = hc' i ≫ ι' i)
    (sqZ'' : ∀ i, ιZ i ≫ h'' = hc'' i ≫ ι'' i)
    (H : ∀ i, IsPushout (hc' i) (hc'' i) (kc' i) (kc'' i)) :
    IsPushout h' h'' k' k'' := by
  classical

  let m : ∀ (l i : 𝒰.I₀), (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange → (𝒰.X l ⟶ 𝒰.X i) :=
    fun l i hli => IsOpenImmersion.lift (𝒰.f i) (𝒰.f l) (by simp at hli ⊢; exact hli)
  have m_fac : ∀ (l i : 𝒰.I₀) (hli : (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange), m l i hli ≫ 𝒰.f i = 𝒰.f l :=
    fun l i hli => IsOpenImmersion.lift_fac _ _ _
  have m_open : ∀ (l i : 𝒰.I₀) (hli : (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange), IsOpenImmersion (m l i hli) := by
    intro l i hli
    have : IsOpenImmersion (m l i hli ≫ 𝒰.f i) := by rw [m_fac l i hli]; infer_instance
    exact IsOpenImmersion.of_comp _ (𝒰.f i)
  let e' : ∀ (l i : 𝒰.I₀), (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange → (X'c l ⟶ X'c i) :=
    fun l i hli => (sq' i).lift (ι' l) (kc' l ≫ m l i hli) (by rw [Category.assoc, m_fac l i hli]; exact (sq' l).w)
  have e'_ι : ∀ l i hli, e' l i hli ≫ ι' i = ι' l := fun l i hli => IsPullback.lift_fst _ _ _ _
  have e'_kc : ∀ l i hli, e' l i hli ≫ kc' i = kc' l ≫ m l i hli := fun l i hli => IsPullback.lift_snd _ _ _ _
  let e'' : ∀ (l i : 𝒰.I₀), (𝒰.f l).opensRange ≤ (𝒰.f i).opensRange → (X''c l ⟶ X''c i) :=
    fun l i hli => (sq'' i).lift (ι'' l) (kc'' l ≫ m l i hli) (by rw [Category.assoc, m_fac l i hli]; exact (sq'' l).w)
  have e''_ι : ∀ l i hli, e'' l i hli ≫ ι'' i = ι'' l := fun l i hli => IsPullback.lift_fst _ _ _ _
  have e''_kc : ∀ l i hli, e'' l i hli ≫ kc'' i = kc'' l ≫ m l i hli := fun l i hli => IsPullback.lift_snd _ _ _ _

  let uc : ∀ (s : PushoutCocone h' h'') (i : 𝒰.I₀), 𝒰.X i ⟶ s.pt := fun s i =>
    (H i).desc (ι' i ≫ s.inl) (ι'' i ≫ s.inr) (by
      rw [← Category.assoc, ← sqZ', Category.assoc, s.condition, ← Category.assoc, sqZ'', Category.assoc])
  have uc_inl : ∀ s i, kc' i ≫ uc s i = ι' i ≫ s.inl := fun s i => IsPushout.inl_desc _ _ _ _
  have uc_inr : ∀ s i, kc'' i ≫ uc s i = ι'' i ≫ s.inr := fun s i => IsPushout.inr_desc _ _ _ _

  have uc_m : ∀ s l i hli, m l i hli ≫ uc s i = uc s l := by
    intro s l i hli
    apply (H l).hom_ext
    · rw [← Category.assoc, ← e'_kc l i hli, Category.assoc, uc_inl s i, ← Category.assoc, e'_ι l i hli, uc_inl s l]
    · rw [← Category.assoc, ← e''_kc l i hli, Category.assoc, uc_inr s i, ← Category.assoc, e''_ι l i hli, uc_inr s l]

  have compat : ∀ s i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ uc s i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ uc s j := by
    intro s i j
    apply hom_ext_of_forall_openImmersion
    intro v
    have hxi : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) v ∈ (𝒰.f i).opensRange := ⟨pullback.fst (𝒰.f i) (𝒰.f j) v, by
      rw [Scheme.Hom.comp_apply]⟩
    have hxj : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) v ∈ (𝒰.f j).opensRange := ⟨pullback.snd (𝒰.f i) (𝒰.f j) v, by
      rw [pullback.condition, Scheme.Hom.comp_apply]⟩
    obtain ⟨l, hxl, hl⟩ := hdir i j _ hxi hxj
    haveI := m_open l i (hl.trans inf_le_left)
    haveI := m_open l j (hl.trans inf_le_right)
    let gl : 𝒰.X l ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      pullback.lift (m l i (hl.trans inf_le_left)) (m l j (hl.trans inf_le_right))
        (by rw [m_fac l i (hl.trans inf_le_left), m_fac l j (hl.trans inf_le_right)])
    have hgl : gl ≫ pullback.fst (𝒰.f i) (𝒰.f j) = m l i (hl.trans inf_le_left) := pullback.lift_fst _ _ _
    haveI : IsOpenImmersion gl := by
      have : IsOpenImmersion (gl ≫ pullback.fst (𝒰.f i) (𝒰.f j)) := by rw [hgl]; infer_instance
      exact IsOpenImmersion.of_comp _ (pullback.fst (𝒰.f i) (𝒰.f j))
    refine ⟨𝒰.X l, gl, inferInstance, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := hxl
      refine ⟨y, (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, hgl, m_fac l i (hl.trans inf_le_left)]
      exact hy
    · rw [← Category.assoc, hgl, uc_m s l i (hl.trans inf_le_left), ← Category.assoc, pullback.lift_snd,
        uc_m s l j (hl.trans inf_le_right)]
  let u : ∀ s : PushoutCocone h' h'', X ⟶ s.pt := fun s => 𝒰.glueMorphisms (uc s) (compat s)
  have u_ι : ∀ s i, 𝒰.f i ≫ u s = uc s i := fun s i => Scheme.Cover.ι_glueMorphisms 𝒰 _ _ i

  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w u ?_ ?_ ?_)
  · intro s
    apply hom_ext_of_forall_openImmersion
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (k' x)
    haveI : IsOpenImmersion (ι' i) := MorphismProperty.of_isPullback (sq' i).flip inferInstance
    refine ⟨X'c i, ι' i, inferInstance, ?_, ?_⟩
    · rw [range_eq_of_isPullback (sq' i)]
      exact ⟨y, hy⟩
    · rw [← Category.assoc, (sq' i).w, Category.assoc, u_ι s i, uc_inl s i]
  · intro s
    apply hom_ext_of_forall_openImmersion
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (k'' x)
    haveI : IsOpenImmersion (ι'' i) := MorphismProperty.of_isPullback (sq'' i).flip inferInstance
    refine ⟨X''c i, ι'' i, inferInstance, ?_, ?_⟩
    · rw [range_eq_of_isPullback (sq'' i)]
      exact ⟨y, hy⟩
    · rw [← Category.assoc, (sq'' i).w, Category.assoc, u_ι s i, uc_inr s i]
  · intro s m₁ h₁ h₂
    apply Scheme.Cover.hom_ext 𝒰
    intro i
    rw [u_ι s i]
    apply (H i).hom_ext
    · rw [← Category.assoc, ← (sq' i).w, Category.assoc, h₁, uc_inl s i]
    · rw [← Category.assoc, ← (sq'' i).w, Category.assoc, h₂, uc_inr s i]

end IsPushout
p2m_export "AlgebraicGeometry" "IsPushout.of_openCover_of_isPullback"
end AlgebraicGeometry

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

theorem surjective_base_specMap {B B' : Type} [CommRing B] [CommRing B'] (φ : B' →+* B)
    (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) :
    Function.Surjective (Spec.map (CommRingCat.ofHom φ)).base := by
  intro x
  obtain ⟨n, hn⟩ := hφn

  have hker : RingHom.ker φ ≤ x.asIdeal := by
    intro b hb
    have hbn : b ^ n ∈ (RingHom.ker φ) ^ n := Ideal.pow_mem_pow hb n
    rw [hn] at hbn
    rw [Ideal.zero_eq_bot, Ideal.mem_bot] at hbn
    exact x.isPrime.mem_of_pow_mem n (by rw [hbn]; exact zero_mem _)
  have hprime : (Ideal.map φ x.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hφs hker
  refine ⟨⟨Ideal.map φ x.asIdeal, hprime⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap φ (Ideal.map φ x.asIdeal) = x.asIdeal
  rw [Ideal.comap_map_of_surjective φ hφs, sup_eq_left]
  intro b hb
  exact hker hb

section Cmp

variable {B B' : Type} [CommRing B] [CommRing B'] (φ : B' →+* B)
  {X Z : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of B')} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (h : Z ⟶ X) (hh : IsPullback h fZ f (Spec.map (CommRingCat.ofHom φ)))

include hh in
theorem isClosedImmersion_cmp (hφs : Function.Surjective φ) : IsClosedImmersion h :=
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφs
  MorphismProperty.of_isPullback hh.flip this

include hh in
theorem surjective_cmp (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) : Surjective h :=
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨surjective_base_specMap φ hφs hφn⟩
  MorphismProperty.of_isPullback hh.flip this

include hh in
theorem bijective_cmp (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) : Function.Bijective h.base :=
  haveI := isClosedImmersion_cmp φ h hh hφs
  ⟨h.isClosedEmbedding.injective, (surjective_cmp φ h hh hφs hφn).1⟩

noncomputable def homeo (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) : ↥Z ≃ₜ ↥X :=
  haveI := isClosedImmersion_cmp φ h hh hφs
  (Equiv.ofBijective h.base (bijective_cmp φ h hh hφs hφn)).toHomeomorphOfIsInducing h.isClosedEmbedding.isInducing

@[scoped simp] theorem homeo_apply (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) (z : Z) :
    homeo φ h hh hφs hφn z = h.base z := rfl

theorem apply_homeo_symm (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker φ)) (x : X) :
    h.base ((homeo φ h hh hφs hφn).symm x) = x :=
  (homeo φ h hh hφs hφn).apply_symm_apply x

end Cmp

section Twin

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B)
  (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
  (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
  {X' X'' Z : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of B')} {f'' : X'' ⟶ Spec (CommRingCat.of B'')}
  {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
  (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ'')))

noncomputable def twin : X'.Opens ≃o X''.Opens :=
  (homeo φ' h' hh' hφ's hφ'n).opensCongr.symm.trans (homeo φ'' h'' hh'' hφ''s hφ''n).opensCongr

theorem twin_def (U : X'.Opens) :
    twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U =
      Opens.comap ((homeo φ'' h'' hh'' hφ''s hφ''n).symm : C(↥X'', ↥Z))
        (Opens.comap ((homeo φ' h' hh' hφ's hφ'n) : C(↥Z, ↥X')) U) := rfl

theorem mem_twin_iff' (U : X'.Opens) (y : X'') :
    y ∈ twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U ↔ h'.base ((homeo φ'' h'' hh'' hφ''s hφ''n).symm y) ∈ U := by
  rw [twin_def]
  simp only [Opens.mem_comap, ContinuousMap.coe_coe, homeo_apply]

theorem mem_twin_iff (U : X'.Opens) (z : Z) :
    h''.base z ∈ twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U ↔ h'.base z ∈ U := by
  rw [mem_twin_iff', ← homeo_apply φ'' h'' hh'' hφ''s hφ''n z, Homeomorph.symm_apply_apply]

theorem preimage_twin (U : X'.Opens) :
    h'' ⁻¹ᵁ (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) = h' ⁻¹ᵁ U := by
  ext z
  exact mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U z

include hh'' hφ''s hφ''n in
theorem preimage_injective {U V : X''.Opens} (e : h'' ⁻¹ᵁ U = h'' ⁻¹ᵁ V) : U = V := by
  ext y
  obtain ⟨z, rfl⟩ := (bijective_cmp φ'' h'' hh'' hφ''s hφ''n).2 y
  change z ∈ h'' ⁻¹ᵁ U ↔ z ∈ h'' ⁻¹ᵁ V
  rw [e]

theorem twin_eq_iff (U : X'.Opens) (U'' : X''.Opens) :
    twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U = U'' ↔ h' ⁻¹ᵁ U = h'' ⁻¹ᵁ U'' := by
  constructor
  · rintro rfl
    exact (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).symm
  · intro e
    apply preimage_injective φ'' hφ''s hφ''n h'' hh''
    rw [preimage_twin, e]

include hh'' hφ''s hφ''n in

theorem twin_basicOpen_eq_basicOpen_of_app_eq {U : X'.Opens} (s : Γ(X', U)) {V'' : X''.Opens} (s'' : Γ(X'', V''))
    (e : Z.basicOpen (h''.app V'' s'') = Z.basicOpen (h'.app U s)) :
    twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (X'.basicOpen s) = X''.basicOpen s'' := by
  rw [twin_eq_iff, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen, e]

include hφ''s in
theorem exists_basicOpen_eq_twin_basicOpen {U : X'.Opens}
    (hU'' : IsAffineOpen (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U)) (s : Γ(X', U)) :
    ∃ s'' : Γ(X'', twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U),
      h''.app _ s'' = Z.presheaf.map (eqToHom (congrArg op (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).symm))
        (h'.app U s) ∧
      twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (X'.basicOpen s) = X''.basicOpen s'' := by
  haveI := isClosedImmersion_cmp φ'' h'' hh'' hφ''s
  obtain ⟨s'', hs''⟩ := h''.app_surjective _ hU''
    (Z.presheaf.map (eqToHom (congrArg op (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).symm)) (h'.app U s))
  refine ⟨s'', hs'', twin_basicOpen_eq_basicOpen_of_app_eq φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' s s'' ?_⟩
  rw [hs'', Scheme.basicOpen_res, inf_eq_right]
  rw [preimage_twin, ← Scheme.preimage_basicOpen]
  exact fun z hz => X'.basicOpen_le s hz

include hφ's hφ'n hh' in
theorem exists_biaffine (x : X') (W : X'.Opens) (hx : x ∈ W) :
    ∃ U : X'.Opens, U ≤ W ∧ x ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) := by
  haveI := isClosedImmersion_cmp φ'' h'' hh'' hφ''s

  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'W⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen

  obtain ⟨z, rfl⟩ := (bijective_cmp φ' h' hh' hφ's hφ'n).2 x
  have hzV'' : h''.base z ∈ twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V' :=
    (mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V' z).mpr hxV'
  obtain ⟨_, ⟨V'', hV'', rfl⟩, hzV''2, hV''le⟩ := X''.isBasis_affineOpens.exists_subset_of_mem_open hzV''
    (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V').isOpen

  let W' : X'.Opens := (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'').symm V''
  have hW' : twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' W' = V'' := OrderIso.apply_symm_apply _ _
  have hxW' : h'.base z ∈ W' := by
    rw [← mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'', hW']
    exact hzV''2
  have hW'V' : W' ≤ V' := by
    rw [← (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'').le_iff_le, hW']
    exact fun y hy => hV''le hy
  obtain ⟨s, hsle, hxs⟩ := hV'.exists_basicOpen_le ⟨h'.base z, hxW'⟩ hxV'

  have hle : h'' ⁻¹ᵁ V'' ≤ h' ⁻¹ᵁ V' := by
    rw [← hW', preimage_twin]
    exact fun z hz => hW'V' hz
  obtain ⟨s'', hs''⟩ := h''.app_surjective V'' hV'' (Z.presheaf.map (homOfLE hle).op (h'.app V' s))
  have htwin : twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (X'.basicOpen s) = X''.basicOpen s'' := by
    apply twin_basicOpen_eq_basicOpen_of_app_eq φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' s s''
    rw [hs'', Scheme.basicOpen_res, inf_eq_right, ← hW', preimage_twin, ← Scheme.preimage_basicOpen]
    exact fun z hz => hsle hz
  refine ⟨X'.basicOpen s, fun y hy => hV'W (hW'V' (hsle hy)), hxs, hV'.basicOpen s, ?_⟩
  rw [htwin]
  exact hV''.basicOpen s''

end Twin

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

section A

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B)
  (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
  (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
  {X' X'' Z : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of B')} {f'' : X'' ⟶ Spec (CommRingCat.of B'')}
  {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
  (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ'')))

local notation "𝔱" => twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''

noncomputable def q' (U : X'.Opens) : Γ(X', U) →+* Γ(Z, h' ⁻¹ᵁ U) :=
  (h'.appLE U (h' ⁻¹ᵁ U) le_rfl).hom

noncomputable def q'' (U : X'.Opens) : Γ(X'', 𝔱 U) →+* Γ(Z, h' ⁻¹ᵁ U) :=
  (h''.appLE (𝔱 U) (h' ⁻¹ᵁ U)
    (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).ge).hom

abbrev P (U : X'.Opens) : Type :=
  ↥(pullbackRing (q' h' U)
    (q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U))

variable {φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''} in
lemma mem_P_iff (U : X'.Opens) (x : Γ(X', U) × Γ(X'', 𝔱 U)) :
    x ∈ pullbackRing (q' h' U)
      (q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) ↔
    q' h' U x.1 =
      q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U x.2 := Iff.rfl

lemma q'_res {U V : X'.Opens} (e : U ≤ V) (a : Γ(X', V)) :
    q' h' U (X'.presheaf.map (homOfLE e).op a) =
      Z.presheaf.map (homOfLE (h'.preimage_mono e)).op
        (q' h' V a) := by
  simp only [q']
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

lemma q''_res {U V : X'.Opens} (e : U ≤ V) (a : Γ(X'', 𝔱 V)) :
    q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U (X''.presheaf.map (homOfLE ((𝔱).monotone e)).op a) =
      Z.presheaf.map (homOfLE (h'.preimage_mono e)).op
        (q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V a) := by
  simp only [q'']
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

noncomputable def res {U V : X'.Opens} (e : U ≤ V) :
    P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V →+* P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U :=
  (RingHom.prod
      ((X'.presheaf.map (homOfLE e).op).hom.comp (pullbackFst _ _))
      ((X''.presheaf.map (homOfLE ((𝔱).monotone e)).op).hom.comp (pullbackSnd _ _))).codRestrict _
    (fun x => by
      change q' h' U (X'.presheaf.map (homOfLE e).op x.1.1) =
        q'' _ _ _ _ _ _ _ _ _ _ U (X''.presheaf.map (homOfLE ((𝔱).monotone e)).op x.1.2)
      rw [q'_res h' e, q''_res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e, (mem_P_iff V x.1).1 x.2])

@[scoped simp] lemma res_apply_fst {U V : X'.Opens} (e : U ≤ V) (x : P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V) :
    (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e x).1.1 = X'.presheaf.map (homOfLE e).op x.1.1 := rfl

@[scoped simp] lemma res_apply_snd {U V : X'.Opens} (e : U ≤ V) (x : P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V) :
    (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e x).1.2 =
      X''.presheaf.map (homOfLE ((𝔱).monotone e)).op x.1.2 := rfl

lemma pullbackFst_comp_res {U V : X'.Opens} (e : U ≤ V) :
    (pullbackFst _ _).comp (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e) =
      (X'.presheaf.map (homOfLE e).op).hom.comp (pullbackFst _ _) := rfl

lemma pullbackSnd_comp_res {U V : X'.Opens} (e : U ≤ V) :
    (pullbackSnd _ _).comp (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e) =
      (X''.presheaf.map (homOfLE ((𝔱).monotone e)).op).hom.comp (pullbackSnd _ _) := rfl

lemma res_refl (U : X'.Opens) :
    res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (le_refl U) = RingHom.id _ := by
  refine RingHom.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
  · simp only [res_apply_fst, RingHom.id_apply]
    have : homOfLE (le_refl U) = 𝟙 U := rfl
    rw [this, op_id, X'.presheaf.map_id]; rfl
  · simp only [res_apply_snd, RingHom.id_apply]
    have : homOfLE ((𝔱).monotone (le_refl U)) = 𝟙 _ := rfl
    rw [this, op_id, X''.presheaf.map_id]; rfl

lemma res_trans {U V W : X'.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) :
    (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e₁).comp
        (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e₂) =
      res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (e₁.trans e₂) := by
  refine RingHom.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
  · simp only [RingHom.comp_apply, res_apply_fst]
    rw [← CommRingCat.comp_apply, ← X'.presheaf.map_comp]; rfl
  · simp only [RingHom.comp_apply, res_apply_snd]
    rw [← CommRingCat.comp_apply, ← X''.presheaf.map_comp]; rfl

omit φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' in
lemma appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e; rfl

omit φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' in
lemma appTop_comp_appLE {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (V : X.Opens) :
    g.appTop ≫ f.appLE ⊤ V le_top = (f ≫ g).appLE ⊤ V le_top := by
  simp only [Scheme.Hom.appLE, ← Category.assoc]
  rfl

omit φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' in

noncomputable def secMap {R : Type} [CommRing R] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appLE ⊤ U le_top

omit φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' in
lemma secMap_map {R : Type} [CommRing R] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    {U V : X.Opens} (e : U ≤ V) : secMap g V ≫ X.presheaf.map (homOfLE e).op = secMap g U := by
  simp only [secMap, Category.assoc, Scheme.Hom.appLE_map]

include hh' in
lemma secMap_comp_q' (U : X'.Opens) :
    secMap f' U ≫ CommRingCat.ofHom (q' h' U) = CommRingCat.ofHom φ' ≫ secMap fZ (h' ⁻¹ᵁ U) := by
  simp only [secMap, q', CommRingCat.ofHom_hom, Category.assoc]
  rw [Scheme.Hom.appLE_comp_appLE _ _ ⊤ U (h' ⁻¹ᵁ U) le_top le_rfl, Scheme.ΓSpecIso_inv_naturality_assoc,
    appTop_comp_appLE]
  congr 1
  exact appLE_congr_hom hh'.w _ _ _ _

include hh'' in
lemma secMap_comp_q'' (U : X'.Opens) :
    secMap f'' (𝔱 U) ≫ CommRingCat.ofHom (q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) =
      CommRingCat.ofHom φ'' ≫ secMap fZ (h' ⁻¹ᵁ U) := by
  simp only [secMap, q'', CommRingCat.ofHom_hom, Category.assoc]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.ΓSpecIso_inv_naturality_assoc, appTop_comp_appLE]
  congr 1
  exact appLE_congr_hom hh''.w _ _ _ _

omit φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' in
theorem isPullback_pullbackRing {A' A'' C : Type} [CommRing A'] [CommRing A''] [CommRing C]
    (q' : A' →+* C) (q'' : A'' →+* C) :
    IsPullback (CommRingCat.ofHom (pullbackFst q' q'')) (CommRingCat.ofHom (pullbackSnd q' q''))
      (CommRingCat.ofHom q') (CommRingCat.ofHom q'') :=
  IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom q') (CommRingCat.ofHom q''))

noncomputable def β (U : X'.Opens) :
    pullbackRing φ' φ'' →+* P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U :=
  (RingHom.prod ((secMap f' U).hom.comp (pullbackFst φ' φ''))
      ((secMap f'' (𝔱 U)).hom.comp (pullbackSnd φ' φ''))).codRestrict _
    (fun x => by
      show q' h' U ((secMap f' U).hom x.1.1) = q'' _ _ _ _ _ _ _ _ _ _ U ((secMap f'' (𝔱 U)).hom x.1.2)
      have e1 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (secMap_comp_q' φ' h' hh' U)) x.1.1
      have e2 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom
        (secMap_comp_q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U)) x.1.2
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e1 e2
      erw [e1, e2]
      exact congrArg _ x.2)

lemma pullbackFst_comp_β (U : X'.Opens) :
    (pullbackFst _ _).comp (β φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) =
      (secMap f' U).hom.comp (pullbackFst φ' φ'') := rfl

lemma pullbackSnd_comp_β (U : X'.Opens) :
    (pullbackSnd _ _).comp (β φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U) =
      (secMap f'' (𝔱 U)).hom.comp (pullbackSnd φ' φ'') := rfl

lemma res_comp_β {U V : X'.Opens} (e : U ≤ V) :
    (res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' e).comp
        (β φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' V) =
      β φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U := by
  refine RingHom.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
  · change X'.presheaf.map (homOfLE e).op (secMap f' V x.1.1) = secMap f' U x.1.1
    rw [← CommRingCat.comp_apply, secMap_map]
  · change X''.presheaf.map (homOfLE ((𝔱).monotone e)).op (secMap f'' (𝔱 V) x.1.2) = secMap f'' (𝔱 U) x.1.2
    rw [← CommRingCat.comp_apply, secMap_map]

end A
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

section A1

theorem isPushout_secMap_appLE {B B' : Type} [CommRing B] [CommRing B'] (φ : B' →+* B)
    {X Z : Scheme.{0}} {g : X ⟶ Spec (CommRingCat.of B')} {gZ : Z ⟶ Spec (CommRingCat.of B)}
    (h : Z ⟶ X) (hh : IsPullback h gZ g (Spec.map (CommRingCat.ofHom φ)))
    (U : X.Opens) (hU : IsAffineOpen U) (V : Z.Opens) (hV : IsAffineOpen V) (e : h ⁻¹ᵁ U = V) :
    IsPushout (CommRingCat.ofHom φ) (secMap g U) (secMap gZ V) (h.appLE U V e.ge) := by
  have hUY : V = h ⁻¹ᵁ U ⊓ gZ ⁻¹ᵁ ⊤ := by simp [e]
  have h0 := ((isIso_pushoutSection_iff hh (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hh le_top le_top hUY (isAffineOpen_top _)
      (isAffineOpen_top _) hU)).flip
  refine h0.of_iso (Scheme.ΓSpecIso (CommRingCat.of B')) (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  · simp [secMap]
  · simp [secMap]
  · simp

end A1
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

noncomputable section

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  (φ' : B' →+* B) (φ'' : B'' →+* B)
  (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
  (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
  {X' X'' Z : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of B')} {f'' : X'' ⟶ Spec (CommRingCat.of B'')}
  {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
  (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ'')))

local notation "𝔱" => twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''

theorem twin_mono {U V : X'.Opens} (h : U ≤ V) : 𝔱 U ≤ 𝔱 V :=
  (twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'').monotone h

variable {φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''}

local notation "𝐏" => P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐫" => res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐭𝐦" => twin_mono φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''

variable (φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'') in

structure Chart where
  U : X'.Opens
  affine : IsAffineOpen U
  affine'' : IsAffineOpen (𝔱 U)

namespace Chart

local notation "𝒞" => Chart φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''

scoped instance : Preorder 𝒞 where
  le c d := ∃ s : Γ(X', d.U), c.U = X'.basicOpen s
  le_refl c := ⟨1, by simp⟩
  le_trans c d k := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    have hs' : X'.basicOpen (X'.presheaf.map (eqToHom (congrArg op ht)) s) = X'.basicOpen s := by
      rw [Scheme.basicOpen_res, inf_eq_right, ← ht]
      exact X'.basicOpen_le s
    obtain ⟨r, hr⟩ := k.affine.basicOpen_basicOpen_is_basicOpen t (X'.presheaf.map (eqToHom (congrArg op ht)) s)
    exact ⟨r, by rw [hr, hs', hs]⟩

theorem le_def (c d : 𝒞) : c ≤ d ↔ ∃ s : Γ(X', d.U), c.U = X'.basicOpen s := Iff.rfl

theorem le_opens {c d : 𝒞} (h : c ≤ d) : c.U ≤ d.U := by
  obtain ⟨s, e⟩ := h
  rw [e]
  exact X'.basicOpen_le s

def inf (c d k : 𝒞) (hc : c ≤ k) (hd : d ≤ k) : 𝒞 where
  U := c.U ⊓ d.U
  affine := by
    obtain ⟨s, hs⟩ := (le_def c k).mp hc
    obtain ⟨t, ht⟩ := (le_def d k).mp hd
    rw [hs, ht, ← Scheme.basicOpen_mul]
    exact k.affine.basicOpen _
  affine'' := by
    obtain ⟨s, hs⟩ := (le_def c k).mp hc
    obtain ⟨t, ht⟩ := (le_def d k).mp hd
    obtain ⟨s'', -, hs''⟩ := exists_basicOpen_eq_twin_basicOpen φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' k.affine'' s
    obtain ⟨t'', -, ht''⟩ := exists_basicOpen_eq_twin_basicOpen φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' k.affine'' t
    rw [OrderIso.map_inf, hs, ht, hs'', ht'', ← Scheme.basicOpen_mul]
    exact k.affine''.basicOpen _

theorem inf_U (c d k : 𝒞) (hc : c ≤ k) (hd : d ≤ k) : (inf c d k hc hd).U = c.U ⊓ d.U := rfl

theorem inf_le_left (c d k : 𝒞) (hc : c ≤ k) (hd : d ≤ k) : inf c d k hc hd ≤ c := by
  obtain ⟨t, ht⟩ := (le_def d k).mp hd
  refine ⟨X'.presheaf.map (homOfLE (le_opens hc)).op t, ?_⟩
  rw [Scheme.basicOpen_res, ← ht]
  rfl

theorem inf_le_right (c d k : 𝒞) (hc : c ≤ k) (hd : d ≤ k) : inf c d k hc hd ≤ d := by
  obtain ⟨s, hs⟩ := (le_def c k).mp hc
  refine ⟨X'.presheaf.map (homOfLE (le_opens hd)).op s, ?_⟩
  rw [Scheme.basicOpen_res, ← hs, inf_comm]
  rfl

abbrev Fobj (c : 𝒞) : Scheme.{0} := Spec (CommRingCat.of (𝐏 c.U))

def Fmap {c d : 𝒞} (h : c.U ≤ d.U) : Fobj c ⟶ Fobj d := Spec.map (CommRingCat.ofHom (𝐫 h))

theorem Fmap_refl (c : 𝒞) : Fmap (le_refl c.U) = 𝟙 (Fobj c) := by
  unfold Fmap
  rw [res_refl]
  exact Spec.map_id _

theorem Fmap_trans {c d k : 𝒞} (h₁ : c.U ≤ d.U) (h₂ : d.U ≤ k.U) : Fmap (h₁.trans h₂) = Fmap h₁ ≫ Fmap h₂ := by
  unfold Fmap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, res_trans]

def F : 𝒞 ⥤ Scheme.{0} where
  obj c := Fobj c
  map f := Fmap (le_opens f.le)
  map_id c := Fmap_refl c
  map_comp _ _ := Fmap_trans _ _

theorem F_obj (c : 𝒞) : (F : 𝒞 ⥤ Scheme.{0}).obj c = Spec (CommRingCat.of (𝐏 c.U)) := rfl

theorem F_map {c d : 𝒞} (f : c ⟶ d) : (F : 𝒞 ⥤ Scheme.{0}).map f = Spec.map (CommRingCat.ofHom (𝐫 (le_opens f.le))) := rfl

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

noncomputable section

theorem surjective_base_specMap_of_forall_isNilpotent {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφs : Function.Surjective φ) (hφn : ∀ x ∈ RingHom.ker φ, IsNilpotent x) :
    Function.Surjective (Spec.map (CommRingCat.ofHom φ)).base := by
  intro x
  have hker : RingHom.ker φ ≤ x.asIdeal := by
    intro b hb
    obtain ⟨n, hn⟩ := hφn b hb
    exact x.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have hprime : (Ideal.map φ x.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hφs hker
  refine ⟨⟨Ideal.map φ x.asIdeal, hprime⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap φ (Ideal.map φ x.asIdeal) = x.asIdeal
  rw [Ideal.comap_map_of_surjective φ hφs, sup_eq_left]
  intro b hb
  exact hker hb

theorem isNilpotent_of_basicOpen_eq_bot {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(X, U))
    (h : X.basicOpen s = ⊥) : IsNilpotent s := by
  rw [← PrimeSpectrum.basicOpen_eq_bot_iff, ← hU.fromSpec_preimage_basicOpen, h]
  rfl

theorem isLocalizationAway_of_eq {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    (e : V = X.basicOpen r) :
    @IsLocalization.Away _ _ r Γ(X, V) _ (X.presheaf.map (homOfLE (e.trans_le (X.basicOpen_le r))).op).hom.toAlgebra := by
  subst e
  exact hU.isLocalization_basicOpen r

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  {φ' : B' →+* B} {φ'' : B'' →+* B}
  {hφ's : Function.Surjective φ'} {hφ''s : Function.Surjective φ''}
  {hφ'n : IsNilpotent (RingHom.ker φ')} {hφ''n : IsNilpotent (RingHom.ker φ'')}
  {X' X'' Z : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of B')} {f'' : X'' ⟶ Spec (CommRingCat.of B'')}
  {fZ : Z ⟶ Spec (CommRingCat.of B)}
  {h' : Z ⟶ X'} {hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ'))}
  {h'' : Z ⟶ X''} {hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))}

local notation "𝔱" => twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐏" => P φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐫" => res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐭𝐦" => twin_mono φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐪''" => q'' φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝒞" => Chart φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''

theorem q'_eq_app (U : X'.Opens) : q' h' U = (h'.app U).hom := by
  unfold q'
  rw [← Scheme.Hom.app_eq_appLE]

theorem q''_apply (U : X'.Opens) (b : Γ(X'', 𝔱 U)) :
    𝐪'' U b = (Z.presheaf.map (homOfLE (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).ge).op).hom
      ((h''.app (𝔱 U)).hom b) := rfl

include hh' hφ's in
theorem q'_surjective {U : X'.Opens} (hU : IsAffineOpen U) : Function.Surjective (q' h' U) := by
  haveI := isClosedImmersion_cmp φ' h' hh' hφ's
  rw [q'_eq_app]
  exact h'.app_surjective U hU

theorem presheaf_map_bijective_of_eq {W W' : Z.Opens} (e : W = W') (g : op W ⟶ op W') :
    Function.Bijective (Z.presheaf.map g).hom := by
  subst e
  rw [show g = 𝟙 _ from Subsingleton.elim _ _, Z.presheaf.map_id]
  exact Function.bijective_id

theorem q''_surjective {U : X'.Opens} (hU'' : IsAffineOpen (𝔱 U)) : Function.Surjective (𝐪'' U) := by
  haveI := isClosedImmersion_cmp φ'' h'' hh'' hφ''s
  intro t
  obtain ⟨t₀, ht₀⟩ := (presheaf_map_bijective_of_eq (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U)
    (homOfLE (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).ge).op).2 t
  obtain ⟨b, hb⟩ := h''.app_surjective _ hU'' t₀
  exact ⟨b, by rw [q''_apply, hb, ht₀]⟩

include hh' hφ's hφ'n in

theorem isNilpotent_of_q'_eq_zero {U : X'.Opens} (hU : IsAffineOpen U) (a : Γ(X', U)) (ha : q' h' U a = 0) :
    IsNilpotent a := by
  apply isNilpotent_of_basicOpen_eq_bot hU
  rw [q'_eq_app] at ha
  have hpre : h' ⁻¹ᵁ X'.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen, show (h'.app U).hom a = 0 from ha, Scheme.basicOpen_zero]
  ext x
  obtain ⟨z, rfl⟩ := (bijective_cmp φ' h' hh' hφ's hφ'n).2 x
  change z ∈ h' ⁻¹ᵁ X'.basicOpen a ↔ _
  rw [hpre]
  rfl

theorem isNilpotent_of_q''_eq_zero {U : X'.Opens} (hU'' : IsAffineOpen (𝔱 U)) (b : Γ(X'', 𝔱 U)) (hb : 𝐪'' U b = 0) :
    IsNilpotent b := by
  apply isNilpotent_of_basicOpen_eq_bot hU''
  have hb0 : (h''.app (𝔱 U)).hom b = 0 := by
    apply (presheaf_map_bijective_of_eq (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U)
      (homOfLE (preimage_twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' U).ge).op).1
    rw [← q''_apply, hb, map_zero]
  have hpre : h'' ⁻¹ᵁ X''.basicOpen b = ⊥ := by
    rw [Scheme.preimage_basicOpen, hb0, Scheme.basicOpen_zero]
  ext x
  obtain ⟨z, rfl⟩ := (bijective_cmp φ'' h'' hh'' hφ''s hφ''n).2 x
  change z ∈ h'' ⁻¹ᵁ X''.basicOpen b ↔ _
  rw [hpre]
  rfl

theorem pullbackFst_surjective {U : X'.Opens} (hU'' : IsAffineOpen (𝔱 U)) :
    Function.Surjective (pullbackFst (q' h' U) (𝐪'' U)) := by
  intro a
  obtain ⟨b, hb⟩ := q''_surjective hU'' (q' h' U a)
  exact ⟨⟨(a, b), hb.symm⟩, rfl⟩

theorem pullbackSnd_surjective {U : X'.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (pullbackSnd (q' h' U) (𝐪'' U)) := by
  intro b
  obtain ⟨a, ha⟩ := q'_surjective (hφ's := hφ's) (hh' := hh') hU (𝐪'' U b)
  exact ⟨⟨(a, b), ha⟩, rfl⟩

theorem isNilpotent_of_mem_ker_pullbackFst {U : X'.Opens} (hU'' : IsAffineOpen (𝔱 U))
    (x : 𝐏 U) (hx : x ∈ RingHom.ker (pullbackFst (q' h' U) (𝐪'' U))) : IsNilpotent x := by
  have hx1 : x.1.1 = 0 := hx
  have hx2 : 𝐪'' U x.1.2 = 0 := by
    rw [← show q' h' U x.1.1 = 𝐪'' U x.1.2 from x.2, hx1, map_zero]
  obtain ⟨n, hn⟩ := isNilpotent_of_q''_eq_zero hU'' x.1.2 hx2
  refine ⟨n + 1, Subtype.ext (Prod.ext ?_ ?_)⟩
  · rw [SubmonoidClass.coe_pow, Prod.pow_fst, hx1, pow_succ, mul_zero]; rfl
  · rw [SubmonoidClass.coe_pow, Prod.pow_snd, pow_succ, hn, zero_mul]; rfl

theorem specMap_comp' {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₂ →+* A₃) (b : A₁ →+* A₂) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

namespace Chart

def ι' (c : 𝒞) : Spec (CommRingCat.of Γ(X', c.U)) ⟶ Fobj c :=
  Spec.map (CommRingCat.ofHom (pullbackFst (q' h' c.U) (𝐪'' c.U)))

def ι'' (c : 𝒞) : Spec (CommRingCat.of Γ(X'', 𝔱 c.U)) ⟶ Fobj c :=
  Spec.map (CommRingCat.ofHom (pullbackSnd (q' h' c.U) (𝐪'' c.U)))

scoped instance isClosedImmersion_ι' (c : 𝒞) : IsClosedImmersion (ι' c) :=
  IsClosedImmersion.spec_of_surjective _ (pullbackFst_surjective c.affine'')

scoped instance isClosedImmersion_ι'' (c : 𝒞) : IsClosedImmersion (ι'' c) :=
  IsClosedImmersion.spec_of_surjective _ (pullbackSnd_surjective (hh' := hh') (hφ's := hφ's) c.affine)

theorem bijective_ι' (c : 𝒞) : Function.Bijective (ι' c).base :=
  ⟨(ι' c).isClosedEmbedding.injective,
    surjective_base_specMap_of_forall_isNilpotent _ (pullbackFst_surjective c.affine'')
      (isNilpotent_of_mem_ker_pullbackFst c.affine'')⟩

def j' (c : 𝒞) : (c.U : Scheme.{0}) ⟶ Fobj c := c.affine.isoSpec.hom ≫ ι' c

def j'' (c : 𝒞) : (𝔱 c.U : Scheme.{0}) ⟶ Fobj c := c.affine''.isoSpec.hom ≫ ι'' c

theorem j'_apply (c : 𝒞) (x : c.U) : (j' c).base x = (ι' c).base (c.affine.isoSpec.hom.base x) := by
  unfold j'
  exact Scheme.Hom.comp_apply (c.affine.isoSpec.hom) (ι' c) x

theorem bijective_j' (c : 𝒞) : Function.Bijective (j' c).base := by
  have e : ⇑(j' c).base = ⇑(ι' c).base ∘ ⇑c.affine.isoSpec.hom.base := funext fun x => j'_apply c x
  rw [e]
  exact (bijective_ι' c).comp c.affine.isoSpec.hom.homeomorph.bijective

theorem homOfLE_j' {c d : 𝒞} (h : c.U ≤ d.U) : X'.homOfLE h ≫ j' d = j' c ≫ Fmap h := by
  unfold j' ι' Fmap
  rw [Category.assoc, specMap_comp', pullbackFst_comp_res, ← specMap_comp', CommRingCat.ofHom_hom, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.isoSpec_hom]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]

theorem homOfLE_j'' {c d : 𝒞} (h : c.U ≤ d.U) : X''.homOfLE (𝐭𝐦 h) ≫ j'' d = j'' c ≫ Fmap h := by
  unfold j'' ι'' Fmap
  rw [Category.assoc, specMap_comp', pullbackSnd_comp_res, ← specMap_comp', CommRingCat.ofHom_hom, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.isoSpec_hom]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]

theorem homOfLE_j'_F {c d : 𝒞} (f : c ⟶ d) : X'.homOfLE (le_opens f.le) ≫ j' d = j' c ≫ (F : 𝒞 ⥤ Scheme.{0}).map f :=
  homOfLE_j' (le_opens f.le)

theorem homOfLE_j''_F {c d : 𝒞} (f : c ⟶ d) :
    X''.homOfLE (𝐭𝐦 (le_opens f.le)) ≫ j'' d = j'' c ≫ (F : 𝒞 ⥤ Scheme.{0}).map f :=
  homOfLE_j'' (le_opens f.le)

theorem Fmap_j'_apply {c d : 𝒞} (h : c.U ≤ d.U) (x : c.U) :
    (Fmap h).base ((j' c).base x) = (j' d).base ⟨x.1, h x.2⟩ := by
  rw [← Scheme.Hom.comp_apply, ← homOfLE_j', Scheme.Hom.comp_apply]
  congr 1
  exact Subtype.ext (Scheme.homOfLE_apply h x)

theorem exists_root {c d : 𝒞} (hcd : c ≤ d) :
    ∃ (s : Γ(X', d.U)) (s'' : Γ(X'', 𝔱 d.U)), q' h' d.U s = 𝐪'' d.U s'' ∧
      c.U = X'.basicOpen s ∧ 𝔱 c.U = X''.basicOpen s'' ∧ h' ⁻¹ᵁ c.U = Z.basicOpen (q' h' d.U s) := by
  obtain ⟨s, hs⟩ := (le_def c d).mp hcd
  obtain ⟨s'', hs''1, hs''2⟩ := exists_basicOpen_eq_twin_basicOpen φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' d.affine'' s
  refine ⟨s, s'', ?_, hs, by rw [hs, hs''2], by rw [hs, Scheme.preimage_basicOpen, q'_eq_app]⟩
  rw [q''_apply, hs''1, ← CommRingCat.comp_apply, ← Z.presheaf.map_comp, q'_eq_app]
  rw [show eqToHom _ ≫ (homOfLE _).op = 𝟙 (op (h' ⁻¹ᵁ d.U)) from Subsingleton.elim _ _, Z.presheaf.map_id]
  rfl

theorem isLocalizationAway_res {c d : 𝒞} (hcd : c ≤ d) :
    ∃ σ : 𝐏 d.U, @IsLocalization.Away _ _ σ (𝐏 c.U) _ (𝐫 (le_opens hcd)).toAlgebra := by
  obtain ⟨s, s'', hσ, hc, hc'', hcZ⟩ := exists_root hcd
  refine ⟨⟨(s, s''), hσ⟩, ?_⟩
  haveI := isClosedImmersion_cmp φ' h' hh' hφ's
  letI a1 : Algebra Γ(Z, h' ⁻¹ᵁ d.U) Γ(Z, h' ⁻¹ᵁ c.U) :=
    (Z.presheaf.map (homOfLE (h'.preimage_mono (le_opens hcd))).op).hom.toAlgebra
  letI a2 : Algebra Γ(X', d.U) Γ(X', c.U) := (X'.presheaf.map (homOfLE (le_opens hcd)).op).hom.toAlgebra
  letI a3 : Algebra Γ(X'', 𝔱 d.U) Γ(X'', 𝔱 c.U) := (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hcd))).op).hom.toAlgebra
  haveI i1 : IsLocalization.Away (q' h' d.U s) Γ(Z, h' ⁻¹ᵁ c.U) :=
    isLocalizationAway_of_eq (d.affine.preimage h') (q' h' d.U s) hcZ
  haveI i2 : IsLocalization.Away s Γ(X', c.U) := isLocalizationAway_of_eq d.affine s hc
  haveI i3 : IsLocalization.Away s'' Γ(X'', 𝔱 c.U) := isLocalizationAway_of_eq d.affine'' s'' hc''
  exact (CerednikDrinfeld.SpecialFormal.ModuliPackage.isLocalization_away_pullbackRing_of_comp_eq
    (q' h' d.U) (𝐪'' d.U) ⟨(s, s''), hσ⟩ Γ(Z, h' ⁻¹ᵁ c.U) Γ(X', c.U) Γ(X'', 𝔱 c.U) (q' h' c.U) (𝐪'' c.U)
    (RingHom.ext fun a => q'_res h' (le_opens hcd) a)
    (RingHom.ext fun b => q''_res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' (le_opens hcd) b)
    (𝐫 (le_opens hcd)) (pullbackFst_comp_res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' _)
    (pullbackSnd_comp_res φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' _)).1

theorem isOpenImmersion_Fmap {c d : 𝒞} (hcd : c ≤ d) : IsOpenImmersion (Fmap (le_opens hcd)) := by
  obtain ⟨σ, hσ⟩ := isLocalizationAway_res hcd
  letI := (𝐫 (le_opens hcd)).toAlgebra
  exact IsOpenImmersion.of_isLocalization σ

scoped instance isOpenImmersion_F_map {c d : 𝒞} (f : c ⟶ d) : IsOpenImmersion ((F : 𝒞 ⥤ Scheme.{0}).map f) :=
  isOpenImmersion_Fmap f.le

scoped instance isLocallyDirected_F : ((F : 𝒞 ⥤ Scheme.{0}) ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro c d k fi fj xi xj e
    obtain ⟨yi, rfl⟩ := (bijective_j' c).2 xi
    obtain ⟨yj, rfl⟩ := (bijective_j' d).2 xj
    change (Fmap (le_opens fi.le)).base ((j' c).base yi) = (Fmap (le_opens fj.le)).base ((j' d).base yj) at e
    rw [Fmap_j'_apply, Fmap_j'_apply] at e
    have hy : yi.1 = yj.1 := congrArg Subtype.val ((bijective_j' k).1 e)
    refine ⟨inf c d k fi.le fj.le, (inf_le_left c d k fi.le fj.le).hom, (inf_le_right c d k fi.le fj.le).hom,
      (j' (inf c d k fi.le fj.le)).base ⟨yi.1, yi.2, hy ▸ yj.2⟩, ?_, ?_⟩
    · change (Fmap (le_opens (inf_le_left c d k fi.le fj.le))).base ((j' (inf c d k fi.le fj.le)).base _) = _
      rw [Fmap_j'_apply]
      rfl
    · change (Fmap (le_opens (inf_le_right c d k fi.le fj.le))).base ((j' (inf c d k fi.le fj.le)).base _) = _
      rw [Fmap_j'_apply]
      congr 1
      exact Subtype.ext hy

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

noncomputable section

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
  {φ' : B' →+* B} {φ'' : B'' →+* B}
  {hφ's : Function.Surjective φ'} {hφ''s : Function.Surjective φ''}
  {hφ'n : IsNilpotent (RingHom.ker φ')} {hφ''n : IsNilpotent (RingHom.ker φ'')}
  {X' X'' Z : Scheme.{0}} {f' : X' ⟶ Spec (CommRingCat.of B')} {f'' : X'' ⟶ Spec (CommRingCat.of B'')}
  {fZ : Z ⟶ Spec (CommRingCat.of B)}
  {h' : Z ⟶ X'} {hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ'))}
  {h'' : Z ⟶ X''} {hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))}

local notation "𝔱" => twin φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝒞" => Chart φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝐭𝐦" => twin_mono φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh''
local notation "𝓕" => (Chart.F (φ' := φ') (φ'' := φ'') (hφ's := hφ's) (hφ''s := hφ''s) (hφ'n := hφ'n)
  (hφ''n := hφ''n) (h' := h') (hh' := hh') (h'' := h'') (hh'' := hh''))

theorem isOpenImmersion_specMap_presheaf_map_of_eq {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U)
    (r : Γ(X, U)) (e : V = X.basicOpen r) (h : V ≤ U) : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op)) := by
  letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  haveI : IsLocalization.Away r Γ(X, V) := isLocalizationAway_of_eq hU r e
  exact IsOpenImmersion.of_isLocalization r

namespace Chart

theorem exists_common_subchart (c d : 𝒞) (x : X') (hc : x ∈ c.U) (hd : x ∈ d.U) :
    ∃ l : 𝒞, l ≤ c ∧ l ≤ d ∧ x ∈ l.U := by
  obtain ⟨s, t, hst, hxs⟩ := exists_basicOpen_le_affine_inter c.affine d.affine x ⟨hc, hd⟩
  obtain ⟨s'', -, hs''⟩ := exists_basicOpen_eq_twin_basicOpen φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' c.affine'' s
  refine ⟨⟨X'.basicOpen s, c.affine.basicOpen s, ?_⟩, ⟨s, rfl⟩, ⟨t, hst⟩, hxs⟩
  rw [hs'']
  exact c.affine''.basicOpen s''

theorem specMap_res_ι' {l c : 𝒞} (h : l.U ≤ c.U) :
    Spec.map (X'.presheaf.map (homOfLE h).op) ≫ ι' c = ι' l ≫ Fmap h := by
  unfold ι' Fmap
  rw [specMap_comp', pullbackFst_comp_res, ← specMap_comp', CommRingCat.ofHom_hom]

theorem specMap_res_ι'' {l c : 𝒞} (h : l.U ≤ c.U) :
    Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 h)).op) ≫ ι'' c = ι'' l ≫ Fmap h := by
  unfold ι'' Fmap
  rw [specMap_comp', pullbackSnd_comp_res, ← specMap_comp', CommRingCat.ofHom_hom]

theorem Fmap_colimit_ι {l c : 𝒞} (hlc : l ≤ c) : Fmap (le_opens hlc) ≫ colimit.ι 𝓕 c = colimit.ι 𝓕 l :=
  colimit.w 𝓕 hlc.hom

theorem isOpenImmersion_specMap_res' {l c : 𝒞} (hlc : l ≤ c) :
    IsOpenImmersion (Spec.map (X'.presheaf.map (homOfLE (le_opens hlc)).op)) := by
  obtain ⟨s, hs⟩ := (le_def l c).mp hlc
  exact isOpenImmersion_specMap_presheaf_map_of_eq c.affine s hs _

theorem isOpenImmersion_specMap_res'' {l c : 𝒞} (hlc : l ≤ c) :
    IsOpenImmersion (Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hlc))).op)) := by
  obtain ⟨s, s'', -, hs, hs'', -⟩ := exists_root hlc
  exact isOpenImmersion_specMap_presheaf_map_of_eq c.affine'' s'' hs'' _

theorem k'_compat_aux (c d : 𝒞) :
    pullback.fst c.affine.fromSpec d.affine.fromSpec ≫ (ι' c ≫ colimit.ι 𝓕 c) =
      pullback.snd c.affine.fromSpec d.affine.fromSpec ≫ (ι' d ≫ colimit.ι 𝓕 d) := by
  apply Scheme.hom_ext_of_forall
  intro w
  have hxc : c.affine.fromSpec.base ((pullback.fst c.affine.fromSpec d.affine.fromSpec).base w) ∈ c.U := by
    have := Set.mem_range_self (f := c.affine.fromSpec.base) ((pullback.fst c.affine.fromSpec d.affine.fromSpec).base w)
    rwa [c.affine.range_fromSpec] at this
  have hxd : c.affine.fromSpec.base ((pullback.fst c.affine.fromSpec d.affine.fromSpec).base w) ∈ d.U := by
    have := Set.mem_range_self (f := d.affine.fromSpec.base) ((pullback.snd c.affine.fromSpec d.affine.fromSpec).base w)
    rw [d.affine.range_fromSpec] at this
    rwa [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨l, hlc, hld, hxl⟩ := exists_common_subchart c d _ hxc hxd

  let u : Spec (CommRingCat.of Γ(X', l.U)) ⟶ pullback c.affine.fromSpec d.affine.fromSpec :=
    pullback.lift (Spec.map (X'.presheaf.map (homOfLE (le_opens hlc)).op)) (Spec.map (X'.presheaf.map (homOfLE (le_opens hld)).op))
      (by rw [c.affine.map_fromSpec l.affine, d.affine.map_fromSpec l.affine])
  have hu1 : u ≫ pullback.fst _ _ = Spec.map (X'.presheaf.map (homOfLE (le_opens hlc)).op) := pullback.lift_fst _ _ _
  have hu2 : u ≫ pullback.snd _ _ = Spec.map (X'.presheaf.map (homOfLE (le_opens hld)).op) := pullback.lift_snd _ _ _
  haveI : IsOpenImmersion (u ≫ pullback.fst c.affine.fromSpec d.affine.fromSpec) := by
    rw [hu1]; exact isOpenImmersion_specMap_res' hlc
  haveI : IsOpenImmersion u := IsOpenImmersion.of_comp u (pullback.fst c.affine.fromSpec d.affine.fromSpec)

  obtain ⟨q, hq⟩ : ∃ q, l.affine.fromSpec.base q = c.affine.fromSpec.base ((pullback.fst c.affine.fromSpec d.affine.fromSpec).base w) := by
    rw [← Set.mem_range (f := l.affine.fromSpec.base) , l.affine.range_fromSpec]; exact hxl
  have hw : u.base q = w := by
    apply (pullback.fst c.affine.fromSpec d.affine.fromSpec ≫ c.affine.fromSpec).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, hu1, c.affine.map_fromSpec l.affine, hq, Scheme.Hom.comp_apply]
  refine ⟨u.opensRange, ⟨q, hw⟩, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, hu1, ← Category.assoc, specMap_res_ι' (le_opens hlc), Category.assoc, Fmap_colimit_ι hlc,
    ← Category.assoc, hu2, ← Category.assoc, specMap_res_ι' (le_opens hld), Category.assoc, Fmap_colimit_ι hld]

theorem k''_compat_aux (c d : 𝒞) :
    pullback.fst c.affine''.fromSpec d.affine''.fromSpec ≫ (ι'' c ≫ colimit.ι 𝓕 c) =
      pullback.snd c.affine''.fromSpec d.affine''.fromSpec ≫ (ι'' d ≫ colimit.ι 𝓕 d) := by
  apply Scheme.hom_ext_of_forall
  intro w

  set y := c.affine''.fromSpec.base ((pullback.fst c.affine''.fromSpec d.affine''.fromSpec).base w) with hy
  have hyc : y ∈ 𝔱 c.U := by
    have := Set.mem_range_self (f := c.affine''.fromSpec.base) ((pullback.fst c.affine''.fromSpec d.affine''.fromSpec).base w)
    rwa [c.affine''.range_fromSpec] at this
  have hyd : y ∈ 𝔱 d.U := by
    have := Set.mem_range_self (f := d.affine''.fromSpec.base) ((pullback.snd c.affine''.fromSpec d.affine''.fromSpec).base w)
    rw [d.affine''.range_fromSpec] at this
    rwa [hy, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨z, hz⟩ := (bijective_cmp φ'' h'' hh'' hφ''s hφ''n).2 y
  have hxc : h'.base z ∈ c.U := (mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' c.U z).1 (hz ▸ hyc)
  have hxd : h'.base z ∈ d.U := (mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' d.U z).1 (hz ▸ hyd)
  obtain ⟨l, hlc, hld, hxl⟩ := exists_common_subchart c d _ hxc hxd
  have hyl : y ∈ 𝔱 l.U := hz ▸ (mem_twin_iff φ' φ'' hφ's hφ''s hφ'n hφ''n h' hh' h'' hh'' l.U z).2 hxl
  let u : Spec (CommRingCat.of Γ(X'', 𝔱 l.U)) ⟶ pullback c.affine''.fromSpec d.affine''.fromSpec :=
    pullback.lift (Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hlc))).op))
      (Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hld))).op))
      (by rw [c.affine''.map_fromSpec l.affine'', d.affine''.map_fromSpec l.affine''])
  have hu1 : u ≫ pullback.fst _ _ = Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hlc))).op) := pullback.lift_fst _ _ _
  have hu2 : u ≫ pullback.snd _ _ = Spec.map (X''.presheaf.map (homOfLE (𝐭𝐦 (le_opens hld))).op) := pullback.lift_snd _ _ _
  haveI : IsOpenImmersion (u ≫ pullback.fst c.affine''.fromSpec d.affine''.fromSpec) := by
    rw [hu1]; exact isOpenImmersion_specMap_res'' hlc
  haveI : IsOpenImmersion u := IsOpenImmersion.of_comp u (pullback.fst c.affine''.fromSpec d.affine''.fromSpec)
  obtain ⟨q, hq⟩ : ∃ q, l.affine''.fromSpec.base q = y := by
    rw [← Set.mem_range (f := l.affine''.fromSpec.base), l.affine''.range_fromSpec]; exact hyl
  have hw : u.base q = w := by
    apply (pullback.fst c.affine''.fromSpec d.affine''.fromSpec ≫ c.affine''.fromSpec).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, hu1, c.affine''.map_fromSpec l.affine'', hq, hy, Scheme.Hom.comp_apply]
  refine ⟨u.opensRange, ⟨q, hw⟩, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, hu1, ← Category.assoc, specMap_res_ι'' (le_opens hlc), Category.assoc, Fmap_colimit_ι hlc,
    ← Category.assoc, hu2, ← Category.assoc, specMap_res_ι'' (le_opens hld), Category.assoc, Fmap_colimit_ι hld]

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

structure GData (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (X' X'' Z : Scheme.{0}) where
  φ' : B' →+* B
  φ'' : B'' →+* B
  hφ's : Function.Surjective φ'
  hφ''s : Function.Surjective φ''
  hφ'n : IsNilpotent (RingHom.ker φ')
  hφ''n : IsNilpotent (RingHom.ker φ'')
  f' : X' ⟶ Spec (CommRingCat.of B')
  f'' : X'' ⟶ Spec (CommRingCat.of B'')
  fZ : Z ⟶ Spec (CommRingCat.of B)
  h' : Z ⟶ X'
  hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ'))
  h'' : Z ⟶ X''
  hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))

namespace GData

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
  (D : GData B B' B'' X' X'' Z)

noncomputable abbrev tw : X'.Opens ≃o X''.Opens :=
  twin D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh''

abbrev Ch : Type := Chart D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh''

abbrev Pr (U : X'.Opens) : Type := P D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U

noncomputable abbrev qq'' (U : X'.Opens) := q'' D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U

noncomputable abbrev bt (U : X'.Opens) := β D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U

noncomputable abbrev Fn : D.Ch ⥤ Scheme.{0} :=
  Chart.F (φ' := D.φ') (φ'' := D.φ'') (hφ's := D.hφ's) (hφ''s := D.hφ''s) (hφ'n := D.hφ'n)
    (hφ''n := D.hφ''n) (h' := D.h') (hh' := D.hh') (h'' := D.h'') (hh'' := D.hh'')

end GData
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

section D

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
  (D : GData B B' B'' X' X'' Z)

namespace Chart

noncomputable def g' (c : D.Ch) : Spec Γ(Z, D.h' ⁻¹ᵁ c.U) ⟶ Spec Γ(X', c.U) :=
  Spec.map (CommRingCat.ofHom (q' D.h' c.U))

noncomputable def g'' (c : D.Ch) : Spec Γ(Z, D.h' ⁻¹ᵁ c.U) ⟶ Spec Γ(X'', D.tw c.U) :=
  Spec.map (CommRingCat.ofHom (D.qq'' c.U))

noncomputable def fc (c : D.Ch) : Fobj c ⟶ Spec (CommRingCat.of ↥(pullbackRing D.φ' D.φ'')) :=
  Spec.map (CommRingCat.ofHom (D.bt c.U))

lemma g'_ι' (c : D.Ch) : g' D c ≫ ι' c = g'' D c ≫ ι'' c := by
  unfold g' g'' ι' ι''
  rw [specMap_comp', specMap_comp']
  congr 2
  exact RingHom.ext fun x => x.2

lemma Fmap_fc {c d : D.Ch} (e : c.U ≤ d.U) : Fmap e ≫ fc D d = fc D c := by
  unfold Fmap fc
  rw [specMap_comp', res_comp_β]

lemma F_map_fc {c d : D.Ch} (g : c ⟶ d) : D.Fn.map g ≫ fc D d = fc D c :=
  Fmap_fc D (le_opens g.le)

lemma affineZ (c : D.Ch) : IsAffineOpen (D.h' ⁻¹ᵁ c.U) :=
  haveI := isClosedImmersion_cmp D.φ' D.h' D.hh' D.hφ's
  c.affine.preimage D.h'

lemma g'_fromSpec (c : D.Ch) : g' D c ≫ c.affine.fromSpec = (affineZ D c).fromSpec ≫ D.h' :=
  IsAffineOpen.SpecMap_appLE_fromSpec D.h' c.affine (affineZ D c) le_rfl

lemma g''_fromSpec (c : D.Ch) : g'' D c ≫ c.affine''.fromSpec = (affineZ D c).fromSpec ≫ D.h'' :=
  IsAffineOpen.SpecMap_appLE_fromSpec D.h'' c.affine'' (affineZ D c) _

end Chart
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

open Chart

private noncomputable def _root_.AlgebraicGeometry.ThickeningGlue.X : Scheme.{0} := colimit D.Fn

p2m_export "AlgebraicGeometry.ThickeningGlue" "X"

noncomputable def ιc (c : D.Ch) : Fobj c ⟶ X D := colimit.ι D.Fn c

scoped instance (c : D.Ch) : IsOpenImmersion (ιc D c) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover D.Fn).f c))

@[reassoc]
lemma Fmap_ιc {c d : D.Ch} (g : c ⟶ d) : D.Fn.map g ≫ ιc D d = ιc D c :=
  colimit.w D.Fn g

noncomputable def coverX : (X D).OpenCover := Scheme.IsLocallyDirected.openCover D.Fn

private noncomputable def _root_.AlgebraicGeometry.ThickeningGlue.f : X D ⟶ Spec (CommRingCat.of ↥(pullbackRing D.φ' D.φ'')) :=
  colimit.desc D.Fn ⟨_, fun c => fc D c, fun c d g => by have h__af := F_map_fc D g; simp at h__af ⊢; exact h__af⟩

p2m_export "AlgebraicGeometry.ThickeningGlue" "f"
@[reassoc (attr := simp)]
lemma ιc_f (c : D.Ch) : ιc D c ≫ f D = fc D c :=
  colimit.ι_desc _ _

noncomputable def coverX' : X'.OpenCover where
  I₀ := D.Ch
  X c := Spec Γ(X', c.U)
  f c := c.affine.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun c => inferInstance⟩
    obtain ⟨U, -, hxU, hU, hU''⟩ :=
      exists_biaffine D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' x ⊤ trivial
    exact ⟨⟨U, hU, hU''⟩, by rw [IsAffineOpen.range_fromSpec]; exact hxU⟩

noncomputable def coverX'' : X''.OpenCover where
  I₀ := D.Ch
  X c := Spec Γ(X'', D.tw c.U)
  f c := c.affine''.fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, fun c => inferInstance⟩
    obtain ⟨z, rfl⟩ := (bijective_cmp D.φ'' D.h'' D.hh'' D.hφ''s D.hφ''n).2 y
    obtain ⟨U, -, hxU, hU, hU''⟩ :=
      exists_biaffine D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' (D.h'.base z) ⊤ trivial
    refine ⟨⟨U, hU, hU''⟩, ?_⟩
    rw [IsAffineOpen.range_fromSpec]
    exact (mem_twin_iff D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U z).2 hxU

noncomputable def coverZ : Z.OpenCover where
  I₀ := D.Ch
  X c := Spec Γ(Z, D.h' ⁻¹ᵁ c.U)
  f c := (affineZ D c).fromSpec
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun z => ?_, fun c => inferInstance⟩
    obtain ⟨U, -, hxU, hU, hU''⟩ :=
      exists_biaffine D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' (D.h'.base z) ⊤ trivial
    exact ⟨⟨U, hU, hU''⟩, by rw [IsAffineOpen.range_fromSpec]; exact hxU⟩

lemma k'_compat (c d : D.Ch) :
    pullback.fst ((coverX' D).f c) ((coverX' D).f d) ≫ (ι' c ≫ ιc D c) =
      pullback.snd ((coverX' D).f c) ((coverX' D).f d) ≫ (ι' d ≫ ιc D d) :=
  Chart.k'_compat_aux c d

lemma k''_compat (c d : D.Ch) :
    pullback.fst ((coverX'' D).f c) ((coverX'' D).f d) ≫ (ι'' c ≫ ιc D c) =
      pullback.snd ((coverX'' D).f c) ((coverX'' D).f d) ≫ (ι'' d ≫ ιc D d) :=
  Chart.k''_compat_aux c d

noncomputable def k' : X' ⟶ X D :=
  (coverX' D).glueMorphisms (fun c => ι' c ≫ ιc D c) (k'_compat D)

noncomputable def k'' : X'' ⟶ X D :=
  (coverX'' D).glueMorphisms (fun c => ι'' c ≫ ιc D c) (k''_compat D)

@[reassoc]
lemma fromSpec_k' (c : D.Ch) : c.affine.fromSpec ≫ k' D = ι' c ≫ ιc D c :=
  (coverX' D).ι_glueMorphisms _ _ c

@[reassoc]
lemma fromSpec_k'' (c : D.Ch) : c.affine''.fromSpec ≫ k'' D = ι'' c ≫ ιc D c :=
  (coverX'' D).ι_glueMorphisms _ _ c

private lemma _root_.AlgebraicGeometry.ThickeningGlue.w : D.h' ≫ k' D = D.h'' ≫ k'' D := by
  refine (coverZ D).hom_ext _ _ fun c => ?_
  change (affineZ D c).fromSpec ≫ D.h' ≫ k' D = (affineZ D c).fromSpec ≫ D.h'' ≫ k'' D
  rw [← Category.assoc, ← g'_fromSpec D, Category.assoc, fromSpec_k', ← Category.assoc, g'_ι' D,
    ← Category.assoc, ← g''_fromSpec D]
  simp only [Category.assoc, fromSpec_k'']

p2m_export "AlgebraicGeometry.ThickeningGlue" "w"

omit D in
lemma fromSpec_top_Spec (R : Type) [CommRing R] :
    (isAffineOpen_top (Spec (CommRingCat.of R))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

lemma fromSpec_f' (c : D.Ch) : c.affine.fromSpec ≫ D.f' = Spec.map (secMap D.f' c.U) := by
  rw [secMap, Spec.map_comp, ← fromSpec_top_Spec,
    IsAffineOpen.SpecMap_appLE_fromSpec D.f' (isAffineOpen_top _) c.affine]

lemma fromSpec_f'' (c : D.Ch) : c.affine''.fromSpec ≫ D.f'' = Spec.map (secMap D.f'' (D.tw c.U)) := by
  rw [secMap, Spec.map_comp, ← fromSpec_top_Spec,
    IsAffineOpen.SpecMap_appLE_fromSpec D.f'' (isAffineOpen_top _) c.affine'']

lemma fromSpec_fZ (c : D.Ch) : (affineZ D c).fromSpec ≫ D.fZ = Spec.map (secMap D.fZ (D.h' ⁻¹ᵁ c.U)) := by
  rw [secMap, Spec.map_comp, ← fromSpec_top_Spec,
    IsAffineOpen.SpecMap_appLE_fromSpec D.fZ (isAffineOpen_top _) (affineZ D c)]

lemma ι'_fc (c : D.Ch) :
    ι' c ≫ fc D c = Spec.map (secMap D.f' c.U) ≫ Spec.map (CommRingCat.ofHom (pullbackFst D.φ' D.φ'')) := by
  unfold ι' fc
  rw [specMap_comp', ← Spec.map_comp, ← CommRingCat.ofHom_hom (secMap D.f' c.U), ← CommRingCat.ofHom_comp]
  rfl

lemma ι''_fc (c : D.Ch) :
    ι'' c ≫ fc D c = Spec.map (secMap D.f'' (D.tw c.U)) ≫ Spec.map (CommRingCat.ofHom (pullbackSnd D.φ' D.φ'')) := by
  unfold ι'' fc
  rw [specMap_comp', ← Spec.map_comp, ← CommRingCat.ofHom_hom (secMap D.f'' _), ← CommRingCat.ofHom_comp]
  rfl

lemma k'_f : k' D ≫ f D = D.f' ≫ Spec.map (CommRingCat.ofHom (pullbackFst D.φ' D.φ'')) := by
  refine (coverX' D).hom_ext _ _ fun c => ?_
  change c.affine.fromSpec ≫ k' D ≫ f D = c.affine.fromSpec ≫ D.f' ≫ _
  rw [fromSpec_k'_assoc, ιc_f, ι'_fc, ← Category.assoc, fromSpec_f']

lemma k''_f : k'' D ≫ f D = D.f'' ≫ Spec.map (CommRingCat.ofHom (pullbackSnd D.φ' D.φ'')) := by
  refine (coverX'' D).hom_ext _ _ fun c => ?_
  change c.affine''.fromSpec ≫ k'' D ≫ f D = c.affine''.fromSpec ≫ D.f'' ≫ _
  rw [fromSpec_k''_assoc, ιc_f, ι''_fc, ← Category.assoc, fromSpec_f'']

end D
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

section D3

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
  (D : GData B B' B'' X' X'' Z)

open Chart

theorem iso_hom_inv_apply {S T : Scheme.{0}} (e : S ≅ T) (y : ↥T) : e.hom (e.inv y) = y := by
  have h1 : (e.inv ≫ e.hom) y = e.hom (e.inv y) := Scheme.Hom.comp_apply _ _ y
  rw [e.inv_hom_id] at h1
  rw [← h1]
  rfl

theorem exists_of_ιc_eq {i j : D.Ch} {xi : ↥(Fobj i)} {xj : ↥(Fobj j)} (h : ιc D i xi = ιc D j xj) :
    ∃ (l : D.Ch) (gi : l ⟶ i) (gj : l ⟶ j) (z : ↥(Fobj l)), D.Fn.map gi z = xi ∧ D.Fn.map gj z = xj :=
  (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := D.Fn)).mp h

theorem ιc_map_apply {l i : D.Ch} (g : l ⟶ i) (z : ↥(Fobj l)) : ιc D i (D.Fn.map g z) = ιc D l z := by
  have h1 : (D.Fn.map g ≫ ιc D i) z = ιc D i (D.Fn.map g z) := Scheme.Hom.comp_apply _ _ z
  rw [Fmap_ιc] at h1
  exact h1.symm

theorem coverX_directed' (i j : D.Ch) (x : ↥(X D)) (hi : x ∈ (ιc D i).opensRange)
    (hj : x ∈ (ιc D j).opensRange) :
    ∃ l : D.Ch, x ∈ (ιc D l).opensRange ∧
      (ιc D l).opensRange ≤ (ιc D i).opensRange ⊓ (ιc D j).opensRange := by
  obtain ⟨p, hp⟩ := hi
  obtain ⟨q, hq⟩ := hj
  obtain ⟨l, gi, gj, z, hzi, hzj⟩ := exists_of_ιc_eq D (hp.trans hq.symm)
  refine ⟨l, ⟨z, ?_⟩, le_inf ?_ ?_⟩
  · rw [← ιc_map_apply D gi z, hzi]
    exact hp
  · rintro _ ⟨y, rfl⟩
    exact ⟨D.Fn.map gi y, ιc_map_apply D gi y⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨D.Fn.map gj y, ιc_map_apply D gj y⟩

theorem Fn_map_j'_apply {l d : D.Ch} (g : l ⟶ d) (w : ↥l.U) :
    D.Fn.map g (j' l w) = j' d (X'.homOfLE (le_opens g.le) w) := by
  have e1 := congrArg (fun k : (↑l.U : Scheme.{0}) ⟶ Fobj d => k w)
    (homOfLE_j'_F (hh' := D.hh') (hh'' := D.hh'') g)
  have e2 : (X'.homOfLE (le_opens g.le) ≫ j' d) w = j' d (X'.homOfLE (le_opens g.le) w) :=
    Scheme.Hom.comp_apply (X'.homOfLE (le_opens g.le)) (j' d) w
  have e3 : (j' l ≫ D.Fn.map g) w = D.Fn.map g (j' l w) := Scheme.Hom.comp_apply (j' l) (D.Fn.map g) w
  exact e3.symm.trans (e1.symm.trans e2)

theorem mem_of_Fn_map_j'_eq {l d : D.Ch} (g : l ⟶ d) (w : ↥l.U) (ŷ : ↥d.U)
    (h : D.Fn.map g (j' l w) = j' d ŷ) : (ŷ : X') ∈ l.U := by
  rw [Fn_map_j'_apply] at h
  have := (bijective_j' d).1 h
  rw [← this, Scheme.homOfLE_apply]
  exact w.2

theorem isPullback_fromSpec_ι'_pf (c : D.Ch) :
    IsPullback c.affine.fromSpec (ι' c) (k' D) (ιc D c) := by
  refine (IsOpenImmersion.isPullback (ι' c) c.affine.fromSpec (ιc D c) (k' D) (fromSpec_k' D c) ?_).flip
  rw [IsAffineOpen.opensRange_fromSpec]
  ext x
  constructor
  · rintro ⟨p, hp⟩

    obtain ⟨d, y, hy⟩ := (coverX' D).exists_eq x
    change d.affine.fromSpec y = x at hy
    have h1 : k' D x = ιc D d (ι' d y) := by
      have := Scheme.Hom.comp_apply d.affine.fromSpec (k' D) y
      rw [fromSpec_k'] at this
      rw [← hy, ← this]
      exact Scheme.Hom.comp_apply _ _ y
    obtain ⟨l, gc, gd, z, hzc, hzd⟩ := exists_of_ιc_eq D (hp.trans h1)
    obtain ⟨w, rfl⟩ := (bijective_j' l).2 z

    have hyŷ : ι' d y = j' d (d.affine.isoSpec.inv y) := by
      rw [j'_apply, iso_hom_inv_apply]
    rw [hyŷ] at hzd
    have hmem := mem_of_Fn_map_j'_eq D gd w _ hzd
    have hx : x = d.U.ι (d.affine.isoSpec.inv y) := by
      rw [← hy, ← IsAffineOpen.isoSpec_inv_ι]
      exact Scheme.Hom.comp_apply _ _ y
    rw [hx, Scheme.Opens.ι_apply]
    exact le_opens gc.le hmem
  · intro hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range ⇑c.affine.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hx
    change k' D (c.affine.fromSpec y) ∈ Set.range ⇑(ιc D c)
    have := Scheme.Hom.comp_apply c.affine.fromSpec (k' D) y
    rw [fromSpec_k'] at this
    rw [← this]
    exact ⟨ι' c y, (Scheme.Hom.comp_apply _ _ y).symm⟩

theorem bijective_ι'' (c : D.Ch) : Function.Bijective ⇑(ι'' c) := by
  have h := (AlgebraicGeometry.isClosedImmersion_and_bijective_specMap_pullbackSnd (q' D.h' c.U) (D.qq'' c.U)
    (q'_surjective (hh' := D.hh') (hφ's := D.hφ's) c.affine)
    (fun a ha => isNilpotent_of_q'_eq_zero (hh' := D.hh') (hφ's := D.hφ's) (hφ'n := D.hφ'n) c.affine a ha)).2.2.2
  unfold ι''
  exact h

theorem j''_apply (c : D.Ch) (x : ↥(D.tw c.U)) : (j'' c) x = (ι'' c) (c.affine''.isoSpec.hom x) := by
  unfold j''
  exact Scheme.Hom.comp_apply c.affine''.isoSpec.hom (ι'' c) x

theorem bijective_j'' (c : D.Ch) : Function.Bijective ⇑(j'' c) := by
  have e : ⇑(j'' c) = ⇑(ι'' c) ∘ ⇑c.affine''.isoSpec.hom := funext fun x => j''_apply D c x
  rw [e]
  exact (bijective_ι'' D c).comp c.affine''.isoSpec.hom.homeomorph.bijective

theorem Fn_map_j''_apply {l d : D.Ch} (g : l ⟶ d) (w : ↥(D.tw l.U)) :
    D.Fn.map g (j'' l w) = j'' d (X''.homOfLE (twin_mono D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh''
      (le_opens g.le)) w) := by
  have e1 := congrArg (fun k : (↑(D.tw l.U) : Scheme.{0}) ⟶ Fobj d => k w)
    (homOfLE_j''_F (hh' := D.hh') (hh'' := D.hh'') g)
  have e2 : (X''.homOfLE (twin_mono D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' (le_opens g.le)) ≫
      j'' d) w = j'' d (X''.homOfLE (twin_mono D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh''
      (le_opens g.le)) w) :=
    Scheme.Hom.comp_apply (X''.homOfLE _) (j'' d) w
  have e3 : (j'' l ≫ D.Fn.map g) w = D.Fn.map g (j'' l w) := Scheme.Hom.comp_apply (j'' l) (D.Fn.map g) w
  exact e3.symm.trans (e1.symm.trans e2)

theorem mem_of_Fn_map_j''_eq {l d : D.Ch} (g : l ⟶ d) (w : ↥(D.tw l.U)) (ŷ : ↥(D.tw d.U))
    (h : D.Fn.map g (j'' l w) = j'' d ŷ) : (ŷ : X'') ∈ D.tw l.U := by
  rw [Fn_map_j''_apply] at h
  have := (bijective_j'' D d).1 h
  rw [← this, Scheme.homOfLE_apply]
  exact w.2

theorem isPullback_fromSpec_ι''_pf (c : D.Ch) :
    IsPullback c.affine''.fromSpec (ι'' c) (k'' D) (ιc D c) := by
  refine (IsOpenImmersion.isPullback (ι'' c) c.affine''.fromSpec (ιc D c) (k'' D) (fromSpec_k'' D c) ?_).flip
  rw [IsAffineOpen.opensRange_fromSpec]
  ext x
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨d, y, hy⟩ := (coverX'' D).exists_eq x
    change d.affine''.fromSpec y = x at hy
    have h1 : k'' D x = ιc D d (ι'' d y) := by
      have := Scheme.Hom.comp_apply d.affine''.fromSpec (k'' D) y
      rw [fromSpec_k''] at this
      rw [← hy, ← this]
      exact Scheme.Hom.comp_apply _ _ y
    obtain ⟨l, gc, gd, z, hzc, hzd⟩ := exists_of_ιc_eq D (hp.trans h1)
    obtain ⟨w, rfl⟩ := (bijective_j'' D l).2 z
    have hyŷ : ι'' d y = j'' d (d.affine''.isoSpec.inv y) := by
      rw [j''_apply, iso_hom_inv_apply]
    rw [hyŷ] at hzd
    have hmem := mem_of_Fn_map_j''_eq D gd w _ hzd
    have hx : x = (D.tw d.U).ι (d.affine''.isoSpec.inv y) := by
      rw [← hy, ← IsAffineOpen.isoSpec_inv_ι]
      exact Scheme.Hom.comp_apply _ _ y
    rw [hx, Scheme.Opens.ι_apply]
    exact (twin_mono D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' (le_opens gc.le)) hmem
  · intro hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range ⇑c.affine''.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hx
    change k'' D (c.affine''.fromSpec y) ∈ Set.range ⇑(ιc D c)
    have := Scheme.Hom.comp_apply c.affine''.fromSpec (k'' D) y
    rw [fromSpec_k''] at this
    rw [← this]
    exact ⟨ι'' c y, (Scheme.Hom.comp_apply _ _ y).symm⟩

end D3
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

theorem chart_package {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
    (D : GData B B' B'' X' X'' Z) (c : D.Ch) :
    IsPullback (Chart.ι' c) (Spec.map (secMap D.f' c.U)) (Chart.fc D c)
      (Spec.map (CommRingCat.ofHom (pullbackFst D.φ' D.φ''))) ∧
    IsPullback (Chart.ι'' c) (Spec.map (secMap D.f'' (D.tw c.U))) (Chart.fc D c)
      (Spec.map (CommRingCat.ofHom (pullbackSnd D.φ' D.φ''))) ∧
    IsPushout (Chart.g' D c) (Chart.g'' D c) (Chart.ι' c) (Chart.ι'' c) := by
  have hco' := isPushout_secMap_appLE D.φ' D.h' D.hh' c.U c.affine (D.h' ⁻¹ᵁ c.U) (Chart.affineZ D c) rfl
  have hco'' := isPushout_secMap_appLE D.φ'' D.h'' D.hh'' (D.tw c.U) c.affine'' (D.h' ⁻¹ᵁ c.U)
    (Chart.affineZ D c) (preimage_twin _ _ _ _ _ _ _ _ _ _ c.U)
  have key := AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
    D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n
    (isPullback_pullbackRing (q' D.h' c.U) (D.qq'' c.U))
    (CommRingCat.ofHom (D.bt c.U)) (secMap D.f' c.U) (secMap D.f'' (D.tw c.U)) (secMap D.fZ (D.h' ⁻¹ᵁ c.U))
    (by rw [← CommRingCat.ofHom_hom (secMap D.f' c.U), ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]; rfl)
    (by rw [← CommRingCat.ofHom_hom (secMap D.f'' _), ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]; rfl)
    (secMap_comp_q' D.φ' D.h' D.hh' c.U).symm
    (secMap_comp_q'' _ _ _ _ _ _ _ _ _ _ c.U).symm
    hco' hco''
  exact key

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

section G

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
  (D : GData B B' B'' X' X'' Z)

open Chart

lemma eq_bt (U : X'.Opens) (a : pullbackRing D.φ' D.φ'' →+* D.Pr U)
    (ha' : (pullbackFst _ _).comp a = (secMap D.f' U).hom.comp (pullbackFst D.φ' D.φ''))
    (ha'' : (pullbackSnd _ _).comp a = (secMap D.f'' (D.tw U)).hom.comp (pullbackSnd D.φ' D.φ'')) :
    a = D.bt U := by
  refine RingHom.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
  · exact (RingHom.congr_fun ha' x).trans (RingHom.congr_fun (pullbackFst_comp_β D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U) x).symm
  · exact (RingHom.congr_fun ha'' x).trans (RingHom.congr_fun (pullbackSnd_comp_β D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' U) x).symm

lemma H' (c : D.Ch) :
    IsPushout (CommRingCat.ofHom D.φ') (CommRingCat.ofHom (secMap D.f' c.U).hom)
      (CommRingCat.ofHom (secMap D.fZ (D.h' ⁻¹ᵁ c.U)).hom) (CommRingCat.ofHom (q' D.h' c.U)) := by
  have h__af := isPushout_secMap_appLE D.φ' D.h' D.hh' c.U c.affine (D.h' ⁻¹ᵁ c.U) (Chart.affineZ D c) rfl
  simp only [CommRingCat.ofHom_hom] at h__af ⊢
  exact h__af

lemma H'' (c : D.Ch) :
    IsPushout (CommRingCat.ofHom D.φ'') (CommRingCat.ofHom (secMap D.f'' (D.tw c.U)).hom)
      (CommRingCat.ofHom (secMap D.fZ (D.h' ⁻¹ᵁ c.U)).hom) (CommRingCat.ofHom (D.qq'' c.U)) := by
  have h__af := (isPushout_secMap_appLE D.φ'' D.h'' D.hh'' (D.tw c.U) c.affine'' (D.h' ⁻¹ᵁ c.U) (Chart.affineZ D c)
      (preimage_twin D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n D.h' D.hh' D.h'' D.hh'' c.U))
  simp only [CommRingCat.ofHom_hom] at h__af ⊢
  exact h__af

lemma flat_secMap' (c : D.Ch) [Flat D.f'] : (secMap D.f' c.U).hom.Flat := by
  have : Flat (c.affine.fromSpec ≫ D.f') := inferInstance
  rw [fromSpec_f'] at this
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this

lemma flat_secMap'' (c : D.Ch) [Flat D.f''] : (secMap D.f'' (D.tw c.U)).hom.Flat := by
  have : Flat (c.affine''.fromSpec ≫ D.f'') := inferInstance
  rw [fromSpec_f''] at this
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this

lemma fp_secMap' (c : D.Ch) [LocallyOfFinitePresentation D.f'] : (secMap D.f' c.U).hom.FinitePresentation := by
  have : LocallyOfFinitePresentation (c.affine.fromSpec ≫ D.f') := inferInstance
  rw [fromSpec_f'] at this
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp this

lemma fp_secMap'' (c : D.Ch) [LocallyOfFinitePresentation D.f''] :
    (secMap D.f'' (D.tw c.U)).hom.FinitePresentation := by
  have : LocallyOfFinitePresentation (c.affine''.fromSpec ≫ D.f'') := inferInstance
  rw [fromSpec_f''] at this
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp this

lemma flat_bt (c : D.Ch) [Flat D.f'] [Flat D.f''] :
    (D.bt c.U).Flat ∧ ((secMap D.f' c.U).hom.FinitePresentation →
      (secMap D.f'' (D.tw c.U)).hom.FinitePresentation → (D.bt c.U).FinitePresentation) := by
  obtain ⟨a, ha', ha'', -, -, -, -, -, hfl, hfp⟩ :=
    RingHom.exists_pullbackRing_isPushout_flat_of_isPushout_of_flat_of_surjective_of_isNilpotent
      D.φ' D.φ'' D.hφ's D.hφ''s D.hφ'n D.hφ''n
      (secMap D.f' c.U).hom (secMap D.f'' (D.tw c.U)).hom (secMap D.fZ (D.h' ⁻¹ᵁ c.U)).hom
      (q' D.h' c.U) (D.qq'' c.U) (H' D c) (H'' D c) (flat_secMap' D c) (flat_secMap'' D c)
  obtain rfl := eq_bt D c.U a ha' ha''
  exact ⟨hfl, hfp⟩

theorem flat_f [Flat D.f'] [Flat D.f''] : Flat (f D) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (coverX D)]
  intro c
  change Flat (ιc D c ≫ f D)
  rw [ιc_f]
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (flat_bt D c).1

theorem locallyOfFinitePresentation_f [Flat D.f'] [Flat D.f'']
    [LocallyOfFinitePresentation D.f'] [LocallyOfFinitePresentation D.f''] :
    LocallyOfFinitePresentation (f D) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation) (coverX D)]
  intro c
  change LocallyOfFinitePresentation (ιc D c ≫ f D)
  rw [ιc_f]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    ((flat_bt D c).2 (fp_secMap' D c) (fp_secMap'' D c))

end G
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry TopologicalSpace Opposite CerednikDrinfeld.SpecialFormal.ModuliPackage"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsOpenImmersion.lift Scheme.basicOpen_res Scheme.forget Surjective IsOpenImmersion.of_comp IsZariskiLocalAtSource.iff_of_openCover Scheme.Hom.isoOpensRange_inv_comp basicOpen_eq_bot_iff Scheme.Hom IsOpenImmersion.of_isLocalization exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE IsAffineOpen.opensRange_fromSpec IsAffineOpen.fromSpec_top isIso_pushoutSection_iff IsAffineOpen.isoSpec_inv_ι Scheme.IsLocallyDirected.ι_eq_ι_iff Scheme.Pullback.range_fst Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsZariskiLocalAtTarget IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.basicOpen_zero Scheme.Hom.comp_base Scheme.homOfLE_apply Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion HasRingHomProperty.Spec_iff isAffineOpen_top Spec.map_id Scheme.Opens.ι_apply IsZariskiLocalAtTarget.of_openCover Scheme.basicOpen_mul IsAffineOpen IsAffineOpen.range_fromSpec Scheme.Opens.toSpecΓ_SpecMap_presheaf_map isIso_pushoutSection_of_isAffineOpen Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.presieve₀_mem_precoverage_iff LocallyOfFinitePresentation Scheme.ΓSpecIso_naturality HasRingHomProperty IsOpenImmersion.lift_fac IsOpenImmersion.isPullback Scheme.Hom.comp_apply Scheme.Hom.appLE range_eq_univ Scheme.ΓSpecIso_inv_naturality_assoc Scheme.Cover Scheme.ΓSpecIso Scheme.IsLocallyDirected.openCover isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent"
namespace ThickeningGlue
p2m_open "AlgebraicGeometry"

section EH

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {X' X'' Z : Scheme.{0}}
  (D : GData B B' B'' X' X'' Z)

open Chart

lemma coverX_f (c : D.Ch) : (coverX D).f c = ιc D c := rfl

theorem isPullback_k' :
    IsPullback (k' D) D.f' (f D) (Spec.map (CommRingCat.ofHom (pullbackFst D.φ' D.φ''))) := by
  refine IsPullback.of_openCover_of_isPullback (k'_f D) (coverX D)
    (Wc := fun c => Spec Γ(X', c.U)) (fun c => c.affine.fromSpec) (fun c => ι' c)
    (fun c => isPullback_fromSpec_ι'_pf D c) (fun c => ?_)
  have key := (chart_package D c).1
  rw [← ιc_f D c, ← fromSpec_f' D c] at key
  exact key

theorem isPullback_k'' :
    IsPullback (k'' D) D.f'' (f D) (Spec.map (CommRingCat.ofHom (pullbackSnd D.φ' D.φ''))) := by
  refine IsPullback.of_openCover_of_isPullback (k''_f D) (coverX D)
    (Wc := fun c => Spec Γ(X'', D.tw c.U)) (fun c => c.affine''.fromSpec) (fun c => ι'' c)
    (fun c => isPullback_fromSpec_ι''_pf D c) (fun c => ?_)
  have key := (chart_package D c).2.1
  rw [← ιc_f D c, ← fromSpec_f'' D c] at key
  exact key

theorem isPushout_k : IsPushout D.h' D.h'' (k' D) (k'' D) :=
  IsPushout.of_openCover_of_isPullback (w D) (coverX D) (coverX_directed' D)
    (Zc := fun c => Spec Γ(Z, D.h' ⁻¹ᵁ c.U)) (X'c := fun c => Spec Γ(X', c.U))
    (X''c := fun c => Spec Γ(X'', D.tw c.U))
    (fun c => g' D c) (fun c => g'' D c) (fun c => ι' c) (fun c => ι'' c)
    (fun c => (affineZ D c).fromSpec) (fun c => c.affine.fromSpec) (fun c => c.affine''.fromSpec)
    (fun c => isPullback_fromSpec_ι'_pf D c) (fun c => isPullback_fromSpec_ι''_pf D c)
    (fun c => (g'_fromSpec D c).symm) (fun c => (g''_fromSpec D c).symm)
    (fun c => (chart_package D c).2.2)

end EH
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

end AlgebraicGeometry.ThickeningGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry.ThickeningGlue.Chart"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing.AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage"

open AlgebraicGeometry.ThickeningGlue in
theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {X' X'' Z : Scheme.{0}} (f' : X' ⟶ Spec (CommRingCat.of B')) (f'' : X'' ⟶ Spec (CommRingCat.of B''))
    (fZ : Z ⟶ Spec (CommRingCat.of B))
    (h' : Z ⟶ X') (hh' : IsPullback h' fZ f' (Spec.map (CommRingCat.ofHom φ')))
    (h'' : Z ⟶ X'') (hh'' : IsPullback h'' fZ f'' (Spec.map (CommRingCat.ofHom φ''))) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (k' : X' ⟶ X) (k'' : X'' ⟶ X),
      IsPullback k' f' f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
      IsPullback k'' f'' f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
      h' ≫ k' = h'' ≫ k'' ∧ IsPushout h' h'' k' k'' ∧
      (Flat f' → Flat f'' → Flat f) ∧
      (Flat f' → Flat f'' → LocallyOfFinitePresentation f' → LocallyOfFinitePresentation f'' →
        LocallyOfFinitePresentation f) := by
  let D : GData B B' B'' X' X'' Z :=
    { φ' := φ', φ'' := φ'', hφ's := hφ's, hφ''s := hφ''s, hφ'n := hφ'n, hφ''n := hφ''n,
      f' := f', f'' := f'', fZ := fZ, h' := h', hh' := hh', h'' := h'', hh'' := hh'' }
  refine ⟨X D, f D, k' D, k'' D, isPullback_k' D, isPullback_k'' D, w D, isPushout_k D,
    fun hf' hf'' => ?_, fun hf' hf'' hp' hp'' => ?_⟩
  · haveI : Flat D.f' := hf'; haveI : Flat D.f'' := hf''
    exact flat_f D
  · haveI : Flat D.f' := hf'; haveI : Flat D.f'' := hf''
    haveI : LocallyOfFinitePresentation D.f' := hp'; haveI : LocallyOfFinitePresentation D.f'' := hp''
    exact locallyOfFinitePresentation_f D

end S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isPullback_isPushout_flat_of_surjective_of_isNilpotent_pullbackRing (solution)
