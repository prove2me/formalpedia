-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8d42310c-746d-51df-9d69-e8da37bbb19c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace BenchR_RLred

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def transportIso {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (ε : X ⟶ Y) (h : ε ≫ b = a)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N) :
    (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N :=
  (pullbackCongr h.symm).app M ≪≫ ((pullbackComp ε b).symm).app M ≪≫ (Scheme.Modules.pullback ε).mapIso φ ≪≫
    (pullbackComp ε b).app N ≪≫ (pullbackCongr h).app N

section away

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (r : S)

noncomputable abbrev locι : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))

noncomputable abbrev Dr : (Spec (CommRingCat.of S)).Opens := PrimeSpectrum.basicOpen r

lemma range_locι : Set.range (locι r).base = (Dr r : Set _) := by
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away r) r

noncomputable def δ : (Dr r : (Spec (CommRingCat.of S)).Opens).toScheme ≅ Spec (CommRingCat.of (Localization.Away r)) :=
  IsOpenImmersion.isoOfRangeEq (Dr r).ι (locι r) (by rw [range_locι, Scheme.Opens.range_ι])

lemma δ_hom_locι : (δ r).hom ≫ locι r = (Dr r).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma exists_awayIso :
    ∃ κ : (f ⁻¹ᵁ Dr r).toScheme ≅ pullback f (locι r),
      κ.hom ≫ pullback.fst f (locι r) = (f ⁻¹ᵁ Dr r).ι ∧
      κ.hom ≫ pullback.snd f (locι r) = (f ∣_ Dr r) ≫ (δ r).hom := by
  have h1 : IsPullback (f ∣_ Dr r) (f ⁻¹ᵁ Dr r).ι (Dr r).ι f := isPullback_morphismRestrict f (Dr r)
  have h2 : IsPullback ((f ∣_ Dr r) ≫ (δ r).hom) (f ⁻¹ᵁ Dr r).ι (locι r) f := by
    refine IsPullback.of_iso h1 (Iso.refl _) (δ r) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [δ_hom_locι]
    · simp
  refine ⟨h2.flip.isoPullback, ?_, ?_⟩
  · simp
  · simp

end away

section piece

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
  (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _) (r : S)

noncomputable abbrev Ur : A.Opens := f ⁻¹ᵁ Dr r

noncomputable def fr : (Ur f r).toScheme ⟶ Spec (CommRingCat.of (Localization.Away r)) :=
  (f ∣_ Dr r) ≫ (δ r).hom

include he in
lemma range_locι_e_subset : Set.range (locι r ≫ e).base ⊆ Set.range (Ur f r).ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  show f.base (e.base ((locι r).base x)) ∈ Dr r
  have : f.base (e.base ((locι r).base x)) = (locι r).base x := by
    change ((locι r) ≫ e ≫ f).base x = (locι r).base x
    rw [he, Category.comp_id]
  rw [this, ← SetLike.mem_coe, ← range_locι]
  exact ⟨x, rfl⟩

noncomputable def er : Spec (CommRingCat.of (Localization.Away r)) ⟶ (Ur f r).toScheme :=
  IsOpenImmersion.lift (Ur f r).ι (locι r ≫ e) (range_locι_e_subset f e he r)

lemma er_ι : er f e he r ≫ (Ur f r).ι = locι r ≫ e := IsOpenImmersion.lift_fac _ _ _

lemma er_fr : er f e he r ≫ fr f r = 𝟙 _ := by
  rw [← cancel_mono (locι r)]
  rw [Category.assoc, fr, Category.assoc, δ_hom_locι, morphismRestrict_ι, ← Category.assoc, er_ι,
    Category.assoc, he, Category.comp_id, Category.id_comp]

lemma fr_appTop_surjective
    (hΓ : Function.Surjective ((pullback.snd f (locι r)).appTop).hom) :
    Function.Surjective ((fr f r).appTop).hom := by
  obtain ⟨κ, hκ₁, hκ₂⟩ := exists_awayIso f r
  have hfr : fr f r = κ.hom ≫ pullback.snd f (locι r) := by rw [hκ₂]; rfl
  rw [hfr, Scheme.Hom.comp_appTop]
  change Function.Surjective ((κ.hom.appTop).hom ∘ (pullback.snd f (locι r)).appTop.hom)
  refine Function.Surjective.comp ?_ hΓ
  intro x
  refine ⟨(κ.inv.appTop).hom x, ?_⟩
  change (κ.inv.appTop ≫ κ.hom.appTop).hom x = x
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

end piece

section nested

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
  (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)

include he in
lemma Dr_le_of_Ur_le {r r' : S} (h : Ur f r' ≤ Ur f r) : Dr r' ≤ Dr r := by
  intro x hx
  have hfe : f.base (e.base x) = x := by
    change (e ≫ f).base x = x
    rw [he]; rfl
  have : e.base x ∈ Ur f r' := by
    show f.base (e.base x) ∈ Dr r'
    rw [hfe]; exact hx
  have := h this
  change f.base (e.base x) ∈ Dr r at this
  rwa [hfe] at this

noncomputable def lam {r r' : S} (h : Dr r' ≤ Dr r) :
    Spec (CommRingCat.of (Localization.Away r')) ⟶ Spec (CommRingCat.of (Localization.Away r)) :=
  (δ r').inv ≫ (Spec (CommRingCat.of S)).homOfLE h ≫ (δ r).hom

lemma lam_locι {r r' : S} (h : Dr r' ≤ Dr r) : lam h ≫ locι r = locι r' := by
  rw [lam, Category.assoc, Category.assoc, δ_hom_locι, Scheme.homOfLE_ι, Iso.inv_comp_eq, δ_hom_locι]

include he in
lemma er_homOfLE {r r' : S} (h : Ur f r' ≤ Ur f r) :
    er f e he r' ≫ A.homOfLE h = lam (Dr_le_of_Ur_le f e he h) ≫ er f e he r := by
  rw [← cancel_mono (Ur f r).ι, Category.assoc, Scheme.homOfLE_ι, er_ι, Category.assoc, er_ι,
    ← Category.assoc, lam_locι]

end nested

end BenchR_RLred

open BenchR_RLred in
theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (hLe : Nonempty ((Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hMe : Nonempty ((Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (hloc : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    Nonempty (L ≅ M) := by
  classical
  obtain ⟨tL⟩ := hLe
  obtain ⟨tM⟩ := hMe

  let I := {r : S // Nonempty ((Scheme.Modules.pullback (Ur f r).ι).obj L ≅ (Scheme.Modules.pullback (Ur f r).ι).obj M)}

  have restr : ∀ {V W : A.Opens} (h : W ≤ V),
      ((Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj M) →
      ((Scheme.Modules.pullback W.ι).obj L ≅ (Scheme.Modules.pullback W.ι).obj M) :=
    fun h ψ => transportIso _ _ (A.homOfLE h) (A.homOfLE_ι h) ψ

  have hex : ∀ i : I, ∃! φ : (Scheme.Modules.pullback (Ur f i.1).ι).obj L ≅ (Scheme.Modules.pullback (Ur f i.1).ι).obj M,
      (Scheme.Modules.pullback (er f e he i.1)).map φ.hom =
        ((Scheme.Modules.pullbackComp (er f e he i.1) (Ur f i.1).ι).app L ≪≫
            (Scheme.Modules.pullbackCongr (er_ι f e he i.1)).app L ≪≫
            ((Scheme.Modules.pullbackComp (locι i.1) e).app L).symm ≪≫ (Scheme.Modules.pullback (locι i.1)).mapIso tL ≪≫
            Scheme.Modules.pullbackUnitIso (locι i.1)).hom ≫
        ((Scheme.Modules.pullbackComp (er f e he i.1) (Ur f i.1).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (er_ι f e he i.1)).app M ≪≫
            ((Scheme.Modules.pullbackComp (locι i.1) e).app M).symm ≪≫ (Scheme.Modules.pullback (locι i.1)).mapIso tM ≪≫
            Scheme.Modules.pullbackUnitIso (locι i.1)).inv :=
    fun i => AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
      e (Ur f i.1).ι (Localization.Away i.1) (fr f i.1) (fr_appTop_surjective f i.1 (hΓ i.1))
      (er f e he i.1) (er_fr f e he i.1) (locι i.1) (er_ι f e he i.1) L M hL tL tM i.2
  choose φ hφ using fun i : I => (hex i).exists

  have hU : ⨆ i : I, Ur f i.1 = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨V, hsV, ⟨ψ⟩⟩ := hloc (f.base a)
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hsr, hrV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hsV V.isOpen
    have hle : Ur f r ≤ f ⁻¹ᵁ V := fun x hx => hrV hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, ⟨restr hle ψ⟩⟩, hsr⟩

  have hB : ∀ i j : I, Ur f i.1 ⊓ Ur f j.1 ≤ ⨆ (k : {k : I // Ur f k.1 ≤ Ur f i.1 ⊓ Ur f j.1}), Ur f k.1.1 := by
    intro i j
    have hk : Ur f (i.1 * j.1) = Ur f i.1 ⊓ Ur f j.1 := by
      show f ⁻¹ᵁ Dr (i.1 * j.1) = f ⁻¹ᵁ Dr i.1 ⊓ f ⁻¹ᵁ Dr j.1
      rw [show Dr (i.1 * j.1) = Dr i.1 ⊓ Dr j.1 from PrimeSpectrum.basicOpen_mul i.1 j.1]
      rfl
    have hki : Ur f (i.1 * j.1) ≤ Ur f i.1 := hk.le.trans inf_le_left
    let k : I := ⟨i.1 * j.1, ⟨restr hki (φ i)⟩⟩
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk.le⟩, hk.symm.le hx⟩

  have he' : ∀ (i j : I) (h : Ur f j.1 ≤ Ur f i.1),
      (Scheme.Modules.pullback (A.homOfLE h)).mapIso (φ i) =
        ((Scheme.Modules.pullbackComp (A.homOfLE h) (Ur f i.1).ι).app L ≪≫
            (Scheme.Modules.pullbackCongr (A.homOfLE_ι h)).app L) ≪≫
          φ j ≪≫
          ((Scheme.Modules.pullbackComp (A.homOfLE h) (Ur f i.1).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (A.homOfLE_ι h)).app M).symm := by
    intro i j h
    set CL := (Scheme.Modules.pullbackComp (A.homOfLE h) (Ur f i.1).ι).app L ≪≫
            (Scheme.Modules.pullbackCongr (A.homOfLE_ι h)).app L with hCL
    set CM := (Scheme.Modules.pullbackComp (A.homOfLE h) (Ur f i.1).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (A.homOfLE_ι h)).app M with hCM
    have hX := AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
      e (Ur f i.1).ι (Ur f j.1).ι (er f e he i.1) (locι i.1) (er_ι f e he i.1)
      (er f e he j.1) (locι j.1) (er_ι f e he j.1)
      (A.homOfLE h) (A.homOfLE_ι h) (lam (Dr_le_of_Ur_le f e he h)) (er_homOfLE f e he h)
      (lam_locι (Dr_le_of_Ur_le f e he h)) L M tL tM (φ i) (hφ i)
    have huniq : CL.symm ≪≫ (Scheme.Modules.pullback (A.homOfLE h)).mapIso (φ i) ≪≫ CM = φ j :=
      (hex j).unique hX (hφ j)
    rw [← huniq]
    ext
    simp
  obtain ⟨F, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
    L M (fun i : I => Ur f i.1) hU hB φ he'
  exact ⟨F⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_locally_of_pullback_section_trivial (solution)
