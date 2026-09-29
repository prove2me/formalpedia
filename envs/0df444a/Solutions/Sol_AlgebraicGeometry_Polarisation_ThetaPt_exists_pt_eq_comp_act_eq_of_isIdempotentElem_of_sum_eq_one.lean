-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/767e7801-fa0a-55ac-b9fd-8e7b0884ef4d

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction
import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one.AlgebraicGeometry.Polarisation TopologicalSpace Opposite"

open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Modules.presheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app IsOpenImmersion Scheme.Hom.comp_base Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Hom.opensRange_pullbackFst range_eq_univ Scheme.Modules.pullbackComp Polarisation.ThetaPt Scheme.Modules.pullbackLocalSection existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection Scheme.Modules.bijective_unit_app_of_le_opensRange Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom.id_app Hom Modules.presheaf Γ Modules.Hom.comp_app Modules.Hom Modules.mapPresheaf_app Modules.Hom.id_app isOpenImmersion_SpecMap_localizationAway basicOpen_zero Hom.comp_base Hom.comp_app basicOpen Modules.pullbackCongr Modules.pullbackPushforwardAdjunction basicOpen_mul Modules Hom.preimage_iSup Hom.opensRange_pullbackFst Opens Modules.pullbackComp Cover Modules.pullbackLocalSection Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot Modules.pullbackComp_hom_app_pullbackLocalSection Modules.bijective_unit_app_of_le_opensRange Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app pullbackCongr pullbackPushforwardAdjunction pullbackId pullbackComp pullbackLocalSection pullbackLocalSection_app existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot pullbackComp_hom_app_pullbackLocalSection bijective_unit_app_of_le_opensRange eq_of_forall_map_homOfLE_eq_and_exists_of_compatible"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pullbackComp_inv_app_app_pullbackLocalSection' {X Y Z : Scheme.{0}} (a₁ : X ⟶ Y) (a₂ : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((pullbackComp a₁ a₂).inv.app M).app (a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U))
        (pullbackLocalSection (a₁ ≫ a₂) s : Γ((Scheme.Modules.pullback (a₁ ≫ a₂)).obj M, a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U))) =
      pullbackLocalSection a₁ (pullbackLocalSection a₂ s) := by
  have hiso : ((pullbackComp a₁ a₂).hom.app M).app (a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U)) ≫
      ((pullbackComp a₁ a₂).inv.app M).app (a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U)) = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app, Scheme.Modules.Hom.id_app]
  have h2 : ((pullbackComp a₁ a₂).inv.app M).app (a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U))
      (((pullbackComp a₁ a₂).hom.app M).app (a₁ ⁻¹ᵁ (a₂ ⁻¹ᵁ U))
        (pullbackLocalSection a₁ (pullbackLocalSection a₂ s))) =
      pullbackLocalSection a₁ (pullbackLocalSection a₂ s) :=
    ConcreteCategory.congr_hom hiso (pullbackLocalSection a₁ (pullbackLocalSection a₂ s))
  rw [pullbackComp_hom_app_pullbackLocalSection] at h2
  exact h2

theorem pullbackCongr_hom_app_top_pullbackLocalSection' {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤ (pullbackLocalSection a s : Γ((Scheme.Modules.pullback a).obj M, ⊤)) =
      (pullbackLocalSection b s : Γ((Scheme.Modules.pullback b).obj M, ⊤)) := by
  subst h
  simp [pullbackCongr]

theorem pullbackComp_inv_app_top_pullbackLocalSection' {X Y Z : Scheme.{0}} (a₁ : X ⟶ Y) (a₂ : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp a₁ a₂).inv.app M).app ⊤
        (pullbackLocalSection (a₁ ≫ a₂) s : Γ((Scheme.Modules.pullback (a₁ ≫ a₂)).obj M, ⊤)) =
      (pullbackLocalSection a₁ (pullbackLocalSection a₂ s : Γ((Scheme.Modules.pullback a₂).obj M, ⊤)) :
        Γ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback a₂).obj M), ⊤)) :=
  pullbackComp_inv_app_app_pullbackLocalSection' a₁ a₂ M ⊤ s

theorem pullbackComp_hom_app_top_pullbackLocalSection' {X Y Z : Scheme.{0}} (a₁ : X ⟶ Y) (a₂ : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp a₁ a₂).hom.app M).app ⊤
        (pullbackLocalSection a₁ (pullbackLocalSection a₂ s : Γ((Scheme.Modules.pullback a₂).obj M, ⊤)) :
          Γ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback a₂).obj M), ⊤)) =
      (pullbackLocalSection (a₁ ≫ a₂) s : Γ((Scheme.Modules.pullback (a₁ ≫ a₂)).obj M, ⊤)) :=
  pullbackComp_hom_app_pullbackLocalSection a₁ a₂ M ⊤ s

theorem pullback_map_app_top_pullbackLocalSection₂' {X Y Z : Scheme.{0}} (a₁ : X ⟶ Y) (a₂ : Y ⟶ Z)
    {M : Z.Modules} {M' : Y.Modules} (φ : (Scheme.Modules.pullback a₂).obj M ⟶ M') (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback a₁).map φ).app ⊤
        (pullbackLocalSection a₁ (pullbackLocalSection a₂ s : Γ((Scheme.Modules.pullback a₂).obj M, ⊤)) :
          Γ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback a₂).obj M), ⊤)) =
      (pullbackLocalSection a₁ (φ.app ⊤ (pullbackLocalSection a₂ s : Γ((Scheme.Modules.pullback a₂).obj M, ⊤))) :
        Γ((Scheme.Modules.pullback a₁).obj M', ⊤)) :=
  (pullbackLocalSection_app a₁ φ (pullbackLocalSection a₂ s : Γ((Scheme.Modules.pullback a₂).obj M, ⊤))).symm

theorem Iso.hom_app_inv_app_apply' {X : Scheme.{0}} {M N : X.Modules} (c : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    c.hom.app U (c.inv.app U x) = x := by
  have h : c.inv.app U ≫ c.hom.app U = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
  exact ConcreteCategory.congr_hom h x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Modules.presheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app IsOpenImmersion Scheme.Hom.comp_base Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Hom.opensRange_pullbackFst range_eq_univ Scheme.Modules.pullbackComp Polarisation.ThetaPt Scheme.Modules.pullbackLocalSection existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection Scheme.Modules.bijective_unit_app_of_le_opensRange Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "translate translate_snd ThetaPt prPt constPtR translate_fst"
namespace ThetaPt
p2m_export "AlgebraicGeometry.Polarisation.ThetaPt" "act pt iso mul inv"
p2m_open "AlgebraicGeometry.Polarisation.ThetaPt AlgebraicGeometry.Polarisation AlgebraicGeometry"

theorem act_eq_top' {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {L : RelativeGroupLaw S f}
    {𝓛 : A.Modules} {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}
    (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ.act s = θ.iso.hom.app ⊤ (Scheme.Modules.pullbackLocalSection (translate f L t θ.pt) s :
      Γ((Scheme.Modules.pullback (translate f L t θ.pt)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) :=
  rfl

end AlgebraicGeometry.Polarisation.ThetaPt

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Modules.presheaf Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app IsOpenImmersion Scheme.Hom.comp_base Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Hom.opensRange_pullbackFst range_eq_univ Scheme.Modules.pullbackComp Polarisation.ThetaPt Scheme.Modules.pullbackLocalSection existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection Scheme.Modules.bijective_unit_app_of_le_opensRange Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible"
namespace Polarisation
p2m_export "AlgebraicGeometry.Polarisation" "translate translate_snd ThetaPt prPt constPtR translate_fst"
namespace ThetaPtGlue
p2m_open "AlgebraicGeometry.Polarisation AlgebraicGeometry"

theorem comp_translate_eq_translate_comp
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {R R' : Type} [CommRing R] [CommRing R']
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (u : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (b : pullback f (u ≫ t) ⟶ pullback f t)
    (hb₁ : b ≫ pullback.fst f t = pullback.fst f (u ≫ t))
    (hb₂ : b ≫ pullback.snd f t = pullback.snd f (u ≫ t) ≫ u)
    (x : SchemeHomOver t f) (x' : SchemeHomOver (u ≫ t) f) (hx : x'.1 = u ≫ x.1) :
    b ≫ translate f L t x = translate f L (u ≫ t) x' ≫ b := by
  symm
  apply pullback.hom_ext
  · rw [Category.assoc, hb₁, translate_fst, Category.assoc, translate_fst]
    have hb : b ≫ (pullback.snd f t ≫ t) = pullback.snd f (u ≫ t) ≫ (u ≫ t) := by
      rw [← Category.assoc, hb₂, Category.assoc]
    have e1 : b ≫ (L.mul _ (prPt f t) (constPtR f t x)).1 =
        (schemeHomOverComp b hb (L.mul _ (prPt f t) (constPtR f t x))).1 := rfl
    rw [e1, L.mul_natural]
    have q1 : schemeHomOverComp b hb (prPt f t) = prPt f (u ≫ t) := Subtype.ext (hb₁)
    have q2 : schemeHomOverComp b hb (constPtR f t x) = constPtR f (u ≫ t) x' := by
      apply Subtype.ext
      change b ≫ (pullback.snd f t ≫ x.1) = pullback.snd f (u ≫ t) ≫ x'.1
      rw [hx, ← Category.assoc, hb₂, Category.assoc]
    rw [q1, q2]
  · rw [Category.assoc, Category.assoc, translate_snd, hb₂, ← Category.assoc, translate_snd]

section Cover

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
  {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
  {m : ℕ} (ε : Fin m → R)
  (b : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t)
  (hb₁ : ∀ j, b j ≫ pullback.fst f t =
    pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))
  (hb₂ : ∀ j, b j ≫ pullback.snd f t =
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))

include hb₁ hb₂ in
theorem piece_eq (j : Fin m) :
    b j = (pullbackLeftPullbackSndIso f t (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))).inv ≫
      pullback.fst (pullback.snd f t) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j))))) := by
  apply pullback.hom_ext
  · rw [hb₁, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  · rw [hb₂, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd]

include hb₁ hb₂ in
theorem isOpenImmersion_piece (j : Fin m) : IsOpenImmersion (b j) := by
  rw [piece_eq f t ε b hb₁ hb₂ j]
  infer_instance

include hb₁ hb₂ in
theorem opensRange_piece [∀ j, IsOpenImmersion (b j)] (j : Fin m) :
    (b j).opensRange = (pullback.snd f t) ⁻¹ᵁ (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) := by
  have e := piece_eq f t ε b hb₁ hb₂ j
  have hrange : (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j))))).opensRange =
      (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) := by
    ext1
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away (ε j)) (ε j)
  rw [← hrange, ← Scheme.Hom.opensRange_pullbackFst]
  ext1
  change Set.range (b j).base = Set.range (pullback.fst (pullback.snd f t)
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))).base
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  exact (pullbackLeftPullbackSndIso f t (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))).inv.surjective

include hb₁ hb₂ in
theorem iSup_opensRange_piece_eq_top [∀ j, IsOpenImmersion (b j)] (hsum : ∑ j, ε j = 1) :
    ⨆ j, (b j).opensRange = ⊤ := by
  have hD : ⨆ j, (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) = ⊤ := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨j, rfl⟩)
  simp_rw [opensRange_piece f t ε b hb₁ hb₂]
  rw [← Scheme.Hom.preimage_iSup]
  erw [hD]
  exact TopologicalSpace.Opens.map_top _

include hb₁ hb₂ in
theorem opensRange_piece_inf_eq_bot [∀ j, IsOpenImmersion (b j)] (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (j l : Fin m) (hjl : j ≠ l) : (b j).opensRange ⊓ (b l).opensRange = ⊥ := by
  rw [opensRange_piece f t ε b hb₁ hb₂ j, opensRange_piece f t ε b hb₁ hb₂ l]
  have hD : (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) ⊓ PrimeSpectrum.basicOpen (ε l) = ⊥ := by
    rw [← PrimeSpectrum.basicOpen_mul, horth j l hjl, PrimeSpectrum.basicOpen_zero]
  refine eq_bot_iff.mpr ?_
  intro x hx
  have h1 : (pullback.snd f t).base x ∈
      (PrimeSpectrum.basicOpen (ε j) : (Spec (CommRingCat.of R)).Opens) ⊓ PrimeSpectrum.basicOpen (ε l) := ⟨hx.1, hx.2⟩
  rw [hD] at h1
  exact False.elim (by simp at h1; exact h1)

end Cover

theorem exists_iso_forall_pullback_mapIso_eq_of_isOpenImmersion
    {X : Scheme.{0}} (M N : X.Modules) {ι : Type} {Y : ι → Scheme.{0}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)]
    (hcov : ⨆ j, (b j).opensRange = ⊤) (hdisj : ∀ j l, j ≠ l → (b j).opensRange ⊓ (b l).opensRange = ⊥)
    (e : ∀ j, (Scheme.Modules.pullback (b j)).obj M ≅ (Scheme.Modules.pullback (b j)).obj N) :
    ∃ φ : M ≅ N, ∀ j, (Scheme.Modules.pullback (b j)).mapIso φ = e j :=
  (Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
    M N b hcov hdisj e).exists

theorem eq_of_forall_pullbackLocalSection_eq
    {X : Scheme.{0}} (M : X.Modules) {ι : Type} {Y : ι → Scheme.{0}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)] (hcov : ⨆ j, (b j).opensRange = ⊤)
    (u v : Γ(M, ⊤))
    (h : ∀ j, Scheme.Modules.pullbackLocalSection (b j) u = Scheme.Modules.pullbackLocalSection (b j) v) :
    u = v := by
  refine (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M (fun j => (b j).opensRange) ⊤
    (fun _ => le_top) (by rw [hcov])).1 u v ?_
  intro j
  apply (Scheme.Modules.bijective_unit_app_of_le_opensRange (b j) M (b j).opensRange le_rfl).1
  have nat := ((Scheme.Modules.pullbackPushforwardAdjunction (b j)).unit.app M).mapPresheaf.naturality
    (homOfLE (le_top (a := (b j).opensRange))).op
  simp only [Scheme.Modules.mapPresheaf_app] at nat
  have hu := ConcreteCategory.congr_hom nat u
  have hv := ConcreteCategory.congr_hom nat v
  change ((Scheme.Modules.pullbackPushforwardAdjunction (b j)).unit.app M).app _ (M.presheaf.map _ u) = _ at hu
  change ((Scheme.Modules.pullbackPushforwardAdjunction (b j)).unit.app M).app _ (M.presheaf.map _ v) = _ at hv
  rw [hu, hv]
  change (Scheme.Modules.presheaf _).map _ (Scheme.Modules.pullbackLocalSection (b j) u) =
    (Scheme.Modules.presheaf _).map _ (Scheme.Modules.pullbackLocalSection (b j) v)
  rw [h j]

section ActChase

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (𝓛 : A.Modules) {R R' : Type} [CommRing R] [CommRing R']
  (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (u : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (b : pullback f (u ≫ t) ⟶ pullback f t)
  (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f (u ≫ t))).obj 𝓛)
  (x : SchemeHomOver t f) (θ' : ThetaPt f L 𝓛 (u ≫ t))
  (H : b ≫ translate f L t x = translate f L (u ≫ t) θ'.pt ≫ b)

def chartIso :
    (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback (translate f L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) :=
  (Scheme.Modules.pullbackComp b (translate f L t x)).app _ ≪≫
    (Scheme.Modules.pullbackCongr H).app _ ≪≫
    ((Scheme.Modules.pullbackComp (translate f L (u ≫ t) θ'.pt) b).app _).symm ≪≫
    (Scheme.Modules.pullback (translate f L (u ≫ t) θ'.pt)).mapIso c ≪≫
    θ'.iso ≪≫ c.symm

include H in
theorem act_app_pullbackLocalSection_eq_of_mapIso_eq
    (ψ : (Scheme.Modules.pullback (translate f L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)
    (hψ : (Scheme.Modules.pullback b).mapIso ψ = chartIso f L 𝓛 t u b c x θ' H)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    θ'.act (c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
        Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
      c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b ((⟨x, ψ⟩ : ThetaPt f L 𝓛 t).act s) :
        Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) := by
  have hmap : (Scheme.Modules.pullback b).map ψ.hom = (chartIso f L 𝓛 t u b c x θ' H).hom := congrArg Iso.hom hψ
  symm
  rw [ThetaPt.act_eq_top', ThetaPt.act_eq_top']
  change c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (ψ.hom.app ⊤
    (Scheme.Modules.pullbackLocalSection (translate f L t x) s :
      Γ((Scheme.Modules.pullback (translate f L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) :
      Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) = _
  rw [← Scheme.Modules.pullback_map_app_top_pullbackLocalSection₂' b (translate f L t x) ψ.hom s, hmap]
  simp only [chartIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  change c.hom.app ⊤ (c.inv.app ⊤ (θ'.iso.hom.app ⊤ ((((Scheme.Modules.pullback (translate f L (u ≫ t) θ'.pt)).map c.hom).app ⊤
    ((((Scheme.Modules.pullbackComp (translate f L (u ≫ t) θ'.pt) b).inv.app _).app ⊤
      ((((Scheme.Modules.pullbackCongr H).hom.app _).app ⊤
        ((((Scheme.Modules.pullbackComp b (translate f L t x)).hom.app _).app ⊤
          (Scheme.Modules.pullbackLocalSection b (Scheme.Modules.pullbackLocalSection (translate f L t x) s :
            Γ((Scheme.Modules.pullback (translate f L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (translate f L t x)).obj
              ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)), ⊤)))))))))))) = _
  erw [Scheme.Modules.pullbackComp_hom_app_top_pullbackLocalSection' b (translate f L t x) _ s]
  rw [Scheme.Modules.pullbackCongr_hom_app_top_pullbackLocalSection' H,
    Scheme.Modules.pullbackComp_inv_app_top_pullbackLocalSection',
    Scheme.Modules.pullback_map_app_top_pullbackLocalSection₂', Scheme.Modules.Iso.hom_app_inv_app_apply']

end ActChase

end AlgebraicGeometry.Polarisation.ThetaPtGlue

open AlgebraicGeometry.Polarisation.ThetaPtGlue

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {m : ℕ} (ε : Fin m → R) (hε : ∀ j, IsIdempotentElem (ε j)) (hsum : ∑ j, ε j = 1)
    (horth : ∀ j l, j ≠ l → ε j * ε l = 0)
    (b : ∀ j, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ⟶ pullback f t)
    (hb₁ : ∀ j, b j ≫ pullback.fst f t =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))
    (hb₂ : ∀ j, b j ≫ pullback.snd f t =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))))
    (c : ∀ j, (Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t))).obj 𝓛)
    (θ' : ∀ j, ThetaPt f L 𝓛 (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t)) :
    ∃ θ : ThetaPt f L 𝓛 t,
      (∀ j, (θ' j).pt.1 = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ θ.pt.1) ∧
      (∀ j (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) (θ.act s) :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤),
        (∀ j, (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s' :
            Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) →
        θ.act s = s') := by
  classical

  obtain ⟨y, hy, -⟩ := AlgebraicGeometry.existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal
    ε hε hsum horth (A := A) (fun j => (θ' j).pt.1)
  have hyf : y ≫ f = t := by
    obtain ⟨z, -, hz⟩ := AlgebraicGeometry.existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal
      ε hε hsum horth (A := Spec (CommRingCat.of S))
      (fun j => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t)
    have h1 : y ≫ f = z := hz _ (fun j => by rw [← Category.assoc, hy j]; exact (θ' j).pt.2)
    have h2 : t = z := hz _ (fun j => rfl)
    rw [h1, ← h2]
  let x : SchemeHomOver t f := ⟨y, hyf⟩

  have H : ∀ j, b j ≫ translate f L t x =
      translate f L (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (ε j)))) ≫ t) (θ' j).pt ≫ b j :=
    fun j => comp_translate_eq_translate_comp f L t _ (b j) (hb₁ j) (hb₂ j) x (θ' j).pt (hy j).symm

  haveI : ∀ j, IsOpenImmersion (b j) := fun j => isOpenImmersion_piece f t ε b hb₁ hb₂ j
  have hcov := iSup_opensRange_piece_eq_top f t ε b hb₁ hb₂ hsum
  have hdisj := opensRange_piece_inf_eq_bot f t ε b hb₁ hb₂ horth

  obtain ⟨ψ, hψ⟩ := exists_iso_forall_pullback_mapIso_eq_of_isOpenImmersion
    ((Scheme.Modules.pullback (translate f L t x)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛))
    ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) b hcov hdisj
    (fun j => chartIso f L 𝓛 t _ (b j) (c j) x (θ' j) (H j))
  let θ : ThetaPt f L 𝓛 t := ⟨x, ψ⟩

  have hii : ∀ j (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
      (θ' j).act ((c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) s :
          Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
        (c j).hom.app ⊤ (Scheme.Modules.pullbackLocalSection (b j) (θ.act s) :
          Γ((Scheme.Modules.pullback (b j)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤)) :=
    fun j s => act_app_pullbackLocalSection_eq_of_mapIso_eq f L 𝓛 t _ (b j) (c j) x (θ' j) (H j) ψ (hψ j) s
  refine ⟨θ, fun j => (hy j).symm, hii, fun s s' hs => ?_⟩

  apply eq_of_forall_pullbackLocalSection_eq _ b hcov
  intro j
  have hinj : Function.Injective ((c j).hom.app ⊤) := by
    intro a a' haa
    have := congrArg ((c j).inv.app ⊤) haa
    simpa [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app] using this
  exact hinj ((hii j s).symm.trans (hs j))

end
end S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_ThetaPt_exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one (solution)
