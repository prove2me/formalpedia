-- Prove2me | solution 1 for AlgebraicGeometry.fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6ef30c19-dbad-528b-9630-36e937b4e779

import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.Flat.Basic
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over

p2m_open "CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits"

namespace P2mVanishingAlongH1

universe u

theorem exists_preimage_of_map_eq_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{u}]
    {S : ShortComplex (Sheaf J Ab.{u})} (hS : S.ShortExact) (Y : C)
    (x : S.X₂.obj.obj (op Y)) (hx : S.g.hom.app (op Y) x = 0) :
    ∃ w, S.f.hom.app (op Y) w = x := by
  let ev : Sheaf J Ab.{u} ⥤ Ab.{u} := sheafToPresheaf J Ab.{u} ⋙ (evaluation _ _).obj (op Y)
  have := isLimitForkMapOfIsLimit' ev S.zero hS.fIsKernel
  have hex := ShortComplex.exact_of_f_is_kernel (S.map ev) this
  rw [ShortComplex.ab_exact_iff] at hex
  exact hex x hx

theorem app_map {C : Type*} [Category C] {J : GrothendieckTopology C} {F G : Sheaf J Ab.{u}}
    (φ : F ⟶ G) {Y Y' : C} (f : Y' ⟶ Y) (t : F.obj.obj (op Y)) :
    φ.hom.app (op Y') (F.obj.map f.op t) = G.obj.map f.op (φ.hom.app (op Y) t) := by
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality]; rfl

theorem map_map {C : Type*} [Category C] {J : GrothendieckTopology C} (F : Sheaf J Ab.{u})
    {Y Y' Y'' : C} (f : Y' ⟶ Y) (k : Y'' ⟶ Y') (t : F.obj.obj (op Y)) :
    F.obj.map k.op (F.obj.map f.op t) = F.obj.map (k ≫ f).op t := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

end P2mVanishingAlongH1

open P2mVanishingAlongH1 in
theorem solution
    (Z₀ : Scheme.{0})
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{0} Ab.{1})} (hS : S.ShortExact)
    (h1 : ∀ Y : Scheme.{0}, (Y ⟶ Z₀) → Subsingleton (S.X₁.obj.obj (op Y)))
    (h2 : ∀ (R : Type) [CommRing R] [Module.Flat ℤ R]
        (s : S.X₂.obj.obj (op (Spec (CommRingCat.of R)))),
      (∀ (Y : Scheme.{0}) (k : Y ⟶ Spec (CommRingCat.of R)), (Y ⟶ Z₀) →
          S.X₂.obj.map k.op s = 0) →
      s ∈ Set.range (S.f.hom.app (op (Spec (CommRingCat.of R)))))
    (h3 : Function.Surjective (S.X₂.obj.map (specZIsTerminal.from Z₀).op)) :
    Function.Surjective (S.g.hom.app (op (Spec (CommRingCat.of ℤ)))) ∧
      Function.Injective (FppfCohomologyLES.cohomologyMap S.f 1) := by
  classical
  set T₀ : Scheme.{0} := Spec (CommRingCat.of ℤ) with hT₀

  suffices hsurj : Function.Surjective (S.g.hom.app (op T₀)) by
    refine ⟨hsurj, ?_⟩
    have hsurj0 : Function.Surjective (FppfCohomologyLES.cohomologyMap S.g 0) := by
      intro y
      obtain ⟨c, hc⟩ := hsurj (FppfBigSiteH0Gm.bigSiteH0SectionsAddEquiv S.X₃ y)
      refine ⟨(FppfBigSiteH0Gm.bigSiteH0SectionsAddEquiv S.X₂).symm c, ?_⟩
      apply (FppfBigSiteH0Gm.bigSiteH0SectionsAddEquiv S.X₃).injective
      rw [FppfBigSiteH0Gm.bigSiteH0SectionsAddEquiv_naturality, AddEquiv.apply_symm_apply]
      exact hc
    have e3 := FppfCohomologyLES.fppf_les_exact_three hS 0 1 rfl
    have e1 := FppfCohomologyLES.fppf_les_exact_one hS 0 1 rfl
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (e1 x).1 hx
    obtain ⟨z, rfl⟩ := hsurj0 y
    exact (e3 (FppfCohomologyLES.cohomologyMap S.g 0 z)).2 ⟨z, rfl⟩

  intro q
  have hepi : Epi S.g := hS.epi_g
  have hls : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' (J := Scheme.fppfTopology.{0}) (A := Ab.{1}) S.g).2 hepi

  set Simg : Sieve T₀ := Presheaf.imageSieve S.g.hom q with hSimg_def
  have hSimg : Simg ∈ Scheme.fppfTopology T₀ := Presheaf.imageSieve_mem _ S.g.hom q

  set π : Z₀ ⟶ T₀ := specZIsTerminal.from Z₀ with hπ
  set S' : Sieve Z₀ := Simg.pullback π with hS'_def
  have hS' : S' ∈ Scheme.fppfTopology Z₀ := Scheme.fppfTopology.pullback_stable π hSimg
  let P : Scheme.{0}ᵒᵖ ⥤ Type 1 := S.X₂.obj ⋙ forget Ab.{1}
  have hP : Presieve.IsSheaf Scheme.fppfTopology P :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget (Scheme.fppfTopology) S.X₂.obj (forget Ab.{1})).1
        S.X₂.property)

  have hmem : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z₀}, S' f →
      ∃ t : S.X₂.obj.obj (op Y), S.g.hom.app (op Y) t = S.X₃.obj.map (f ≫ π).op q :=
    fun hf => hf
  let x : Presieve.FamilyOfElements P S'.arrows := fun Y f hf => (hmem hf).choose
  have hx_spec : ∀ {Y : Scheme.{0}} (f : Y ⟶ Z₀) (hf : S' f),
      S.g.hom.app (op Y) (x f hf) = S.X₃.obj.map (f ≫ π).op q :=
    fun f hf => (hmem hf).choose_spec

  have hlift_unique : ∀ {Y : Scheme.{0}} (_ : Y ⟶ Z₀) (t₁ t₂ : S.X₂.obj.obj (op Y)),
      S.g.hom.app (op Y) t₁ = S.g.hom.app (op Y) t₂ → t₁ = t₂ := by
    intro Y z t₁ t₂ ht
    have h0 : S.g.hom.app (op Y) (t₁ - t₂) = 0 := by rw [map_sub, ht, sub_self]
    obtain ⟨w, hw⟩ := exists_preimage_of_map_eq_zero hS Y (t₁ - t₂) h0
    haveI := h1 Y z
    have hw0 : w = 0 := Subsingleton.elim _ _
    rw [hw0, map_zero] at hw
    exact (sub_eq_zero.mp hw.symm)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Y' f k hf
    show x (k ≫ f) (S'.downward_closed hf k) = S.X₂.obj.map k.op (x f hf)
    apply hlift_unique (k ≫ f)
    rw [hx_spec (k ≫ f) (S'.downward_closed hf k), app_map, hx_spec f hf, map_map, Category.assoc]
  let cbar : S.X₂.obj.obj (op Z₀) := (hP S' hS').amalgamate x hx
  have hcbar : ∀ {Y : Scheme.{0}} (f : Y ⟶ Z₀) (hf : S' f), S.X₂.obj.map f.op cbar = x f hf :=
    fun f hf => (hP S' hS').isAmalgamation hx f hf

  obtain ⟨c, hc⟩ := h3 cbar

  suffices hq : q - S.g.hom.app (op T₀) c = 0 by exact ⟨c, (sub_eq_zero.mp hq).symm⟩
  set q' := q - S.g.hom.app (op T₀) c with hq'_def

  have hkey : ∀ (V : Scheme.{0}) [IsAffine V] (h : V ⟶ T₀), Flat h → Simg h →
      S.X₃.obj.map h.op q' = 0 := by
    intro V _ h hflat hh
    obtain ⟨s, hs⟩ : ∃ s : S.X₂.obj.obj (op V), S.g.hom.app (op V) s = S.X₃.obj.map h.op q := hh

    let R : Type := Γ(V, ⊤)
    let e : V ≅ Spec (CommRingCat.of R) := V.isoSpec

    haveI : Module.Flat ℤ R := by
      have hcomp : Flat (e.inv ≫ h) := inferInstance
      have heq : e.inv ≫ h = Spec.map (CommRingCat.ofHom (Int.castRingHom R)) :=
        specZIsTerminal.hom_ext _ _
      rw [heq, HasRingHomProperty.Spec_iff (P := @Flat)] at hcomp
      have hfl : (Int.castRingHom R).Flat := hcomp
      dsimp only [RingHom.Flat] at hfl
      convert hfl <;> first | rfl | exact Subsingleton.elim _ _

    let σ : S.X₂.obj.obj (op (Spec (CommRingCat.of R))) :=
      S.X₂.obj.map e.inv.op (s - S.X₂.obj.map h.op c)
    have hσ : ∀ (Y : Scheme.{0}) (k : Y ⟶ Spec (CommRingCat.of R)), (Y ⟶ Z₀) →
        S.X₂.obj.map k.op σ = 0 := by
      intro Y k z

      let k' : Y ⟶ V := k ≫ e.inv
      have hzπ : z ≫ π = k' ≫ h := specZIsTerminal.hom_ext _ _
      have hz : S' z := by
        show ∃ t, S.g.hom.app (op Y) t = S.X₃.obj.map (z ≫ π).op q
        exact ⟨S.X₂.obj.map k'.op s, by rw [hzπ, app_map, hs, map_map]⟩

      have h_eq : S.X₂.obj.map k'.op s = x z hz := by
        apply hlift_unique z
        rw [hx_spec z hz, hzπ, app_map, hs, map_map]
      have h_c : S.X₂.obj.map k'.op (S.X₂.obj.map h.op c) = x z hz := by
        rw [← hcbar z hz, ← hc, map_map, map_map, hzπ]
      show S.X₂.obj.map k.op (S.X₂.obj.map e.inv.op (s - S.X₂.obj.map h.op c)) = 0
      rw [map_map, map_sub]
      change S.X₂.obj.map k'.op s - S.X₂.obj.map k'.op (S.X₂.obj.map h.op c) = 0
      rw [h_eq, h_c, sub_self]
    obtain ⟨w, hw⟩ := h2 R σ hσ

    have hgσ : S.g.hom.app _ σ = 0 := by
      rw [← hw, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app]
      have hfg : S.f.hom ≫ S.g.hom = (S.f ≫ S.g).hom := rfl
      rw [hfg, S.zero]
      simp

    have h1' : S.X₃.obj.map e.inv.op (S.X₃.obj.map h.op q') = 0 := by
      have : S.X₃.obj.map h.op q' = S.g.hom.app (op V) (s - S.X₂.obj.map h.op c) := by
        rw [hq'_def, map_sub, map_sub, hs, app_map]
      rw [this, ← app_map, hgσ]
    have : S.X₃.obj.map h.op q' =
        S.X₃.obj.map e.hom.op (S.X₃.obj.map e.inv.op (S.X₃.obj.map h.op q')) := by
      rw [map_map, Iso.hom_inv_id]
      simp
    rw [this, h1', map_zero]

  obtain ⟨R₀, hR₀, hle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := Scheme.fppfPrecoverage.{0})).1 hSimg
  have hR₀' : R₀ ∈ Scheme.jointlySurjectivePrecoverage T₀ ∧
      R₀ ∈ (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{0}).precoverage T₀ :=
    hR₀
  have hjs := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hR₀'.1
  have hprop : ∀ {Y : Scheme.{0}} {f : Y ⟶ T₀}, R₀ f →
      Flat f ∧ LocallyOfFinitePresentation f := fun hf => hR₀'.2 hf

  let ι : Type 1 := Σ (Y : Scheme.{0}), Σ' (f : Y ⟶ T₀) (_ : R₀ f), Y.affineOpens
  let Xf : ι → Scheme.{0} := fun i => ((i.2.2.2 : i.1.Opens) : Scheme.{0})
  let ff : ∀ i, Xf i ⟶ T₀ := fun i => (i.2.2.2 : i.1.Opens).ι ≫ i.2.1
  have hR₁ : Presieve.ofArrows Xf ff ∈ Scheme.fppfPrecoverage T₀ := by
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun t => ?_, fun i => ?_⟩
    · obtain ⟨Y, f, hf, y, rfl⟩ := hjs t
      change ↥Y at y
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← iSup_affineOpens_eq_top Y, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨U, hyU⟩ := hy
      exact ⟨⟨Y, f, hf, U⟩, ⟨y, hyU⟩, rfl⟩
    · obtain ⟨Y, f, hf, U⟩ := i
      obtain ⟨_, _⟩ := hprop hf
      exact ⟨inferInstance, inferInstance⟩

  have hP₃ : Presieve.IsSheaf Scheme.fppfTopology (S.X₃.obj ⋙ forget Ab.{1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget (Scheme.fppfTopology) S.X₃.obj (forget Ab.{1})).1
        S.X₃.property)
  refine (hP₃.isSheafFor_of_mem_precoverage hR₁).isSeparatedFor.ext ?_
  rintro _ _ ⟨i⟩
  obtain ⟨Y, f, hf, U⟩ := i
  obtain ⟨_, _⟩ := hprop hf
  haveI : IsAffine ((U : Y.Opens) : Scheme.{0}) := U.2
  have hflat : Flat ((U : Y.Opens).ι ≫ f) := inferInstance
  have hmemU : Simg ((U : Y.Opens).ι ≫ f) := Simg.downward_closed (hle _ _ hf) _
  change S.X₃.obj.map ((U : Y.Opens).ι ≫ f).op q' = S.X₃.obj.map ((U : Y.Opens).ι ≫ f).op 0
  rw [map_zero]
  exact hkey _ ((U : Y.Opens).ι ≫ f) hflat hmemU

end S_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
end P2MW
export P2MW.S_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over (solution)
