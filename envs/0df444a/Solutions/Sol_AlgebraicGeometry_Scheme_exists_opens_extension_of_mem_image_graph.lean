-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/62c856b9-42e5-52c3-96fe-fbcd850182d7

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift IsImmersion.of_comp Scheme.fromSpecStalk_closedPoint Scheme.Hom.isoOpensRange_inv_comp Scheme.Opens.range_ι Scheme.Hom IsOpenImmersion.of_isLocalization Scheme.SpecMap_stalkSpecializes_fromSpecStalk Scheme.range_fromSpecStalk QuasiCompact Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Scheme.Opens.fromSpecStalkOfMem_ι ext_of_isDominant_of_isSeparated IsOpenImmersion Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion isIntegral_of_isOpenImmersion IsReduced IsSeparated QuasiCompact.of_comp IsImmersion Spec.map_id Scheme.SpecMap_stalkMap_fromSpecStalk Spec_closedPoint IsDominant genericPoint_eq_bot_of_affine IsOpenImmersion.lift_uniq Scheme.Opens Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.Opens.iSupOpenCover isReduced_of_isOpenImmersion Scheme.Hom.toImage_imageι IsOpenImmersion.lift_fac Scheme.Cover Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint Scheme.exists_opens_extension_of_fromSpecStalk"
namespace HeckeExt
p2m_open "AlgebraicGeometry"

theorem isIntegral_image_and_birational
    {X P G : Scheme.{u}} [IsIntegral X] [IsIntegral G] (graph : X ⟶ P) [QuasiCompact graph] [IsImmersion graph]
    (p : P ⟶ G) (j : X ⟶ G) [IsOpenImmersion j] (hj : graph ≫ p = j) :
    ∃ (_ : IsIntegral graph.image), (graph.imageι ≫ p).base (genericPoint graph.image) = genericPoint G ∧
      IsIso ((graph.imageι ≫ p).stalkMap (genericPoint graph.image)) ∧
      graph.toImage.base (genericPoint X) = genericPoint graph.image := by
  subst hj
  obtain ⟨hint, hgen, hbir⟩ :=
    AlgebraicGeometry.Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint graph
  haveI := hint
  haveI := hbir
  have hfac : graph.toImage ≫ graph.imageι ≫ p = graph ≫ p := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  refine ⟨hint, ?_, ?_, hgen⟩
  · rw [← hgen]
    have e1 : (graph.imageι ≫ p).base (graph.toImage.base (genericPoint X)) =
        (graph.toImage ≫ graph.imageι ≫ p).base (genericPoint X) := rfl
    rw [e1, hfac]
    exact genericPoint_eq_of_isOpenImmersion (graph ≫ p)
  · have key : IsIso ((graph.toImage ≫ graph.imageι ≫ p).stalkMap (genericPoint X)) := by
      rw [hfac]; infer_instance
    have key' : IsIso ((graph.imageι ≫ p).stalkMap (graph.toImage.base (genericPoint X)) ≫
        graph.toImage.stalkMap (genericPoint X)) := by
      rw [← Scheme.Hom.stalkMap_comp]; exact key
    have hA : IsIso ((graph.imageι ≫ p).stalkMap (graph.toImage.base (genericPoint X))) :=
      (isIso_comp_right_iff _ (graph.toImage.stalkMap (genericPoint X))).mp key'
    rw [hgen] at hA
    exact hA

theorem exists_opens_extension_near_of_birational
    {S G Γ H : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G) (q : Γ ⟶ H) (sG : G ⟶ S) (sH : H ⟶ S)
    [LocallyOfFiniteType sH]
    (hπq : q ≫ sH = π ≫ sG) (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ) [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    ∃ (w : Spec (G.presheaf.stalk (π.base γ)) ⟶ Γ) (U : G.Opens) (hηU : π.base γ ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      w ≫ π = G.fromSpecStalk (π.base γ) ∧ v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem (π.base γ) hηU ≫ v = w ≫ q ∧
      w.base (IsLocalRing.closedPoint _) = γ ∧
      w.base (genericPoint (Spec (G.presheaf.stalk (π.base γ)))) = genericPoint Γ := by

  have hne : γ ≠ genericPoint Γ := by
    intro h
    apply IsDiscreteValuationRing.not_isField (G.presheaf.stalk (π.base γ))
    have hγ' : π.base γ = genericPoint G := by rw [h]; exact hgen
    rw [hγ']
    exact Field.toIsField G.functionField
  haveI : IsIso (π.stalkMap γ) :=
    AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint π hgen hbir γ hne

  let w : Spec (G.presheaf.stalk (π.base γ)) ⟶ Γ := Spec.map (inv (π.stalkMap γ)) ≫ Γ.fromSpecStalk γ
  have hwπ : w ≫ π = G.fromSpecStalk (π.base γ) := by
    show (Spec.map (inv (π.stalkMap γ)) ≫ Γ.fromSpecStalk γ) ≫ π = _
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hwγ : w.base (IsLocalRing.closedPoint _) = γ := by
    show (Spec.map (inv (π.stalkMap γ)) ≫ Γ.fromSpecStalk γ).base _ = _
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    have h1 : (Spec.map (inv (π.stalkMap γ))).base (IsLocalRing.closedPoint _) =
        IsLocalRing.closedPoint _ := Spec_closedPoint
    erw [h1]
    exact Scheme.fromSpecStalk_closedPoint
  have hwξ : w.base (genericPoint (Spec (G.presheaf.stalk (π.base γ)))) = genericPoint Γ := by

    have h1 : (Spec.map (inv (π.stalkMap γ))).base (genericPoint (Spec (G.presheaf.stalk (π.base γ)))) =
        genericPoint (Spec (Γ.presheaf.stalk γ)) :=
      genericPoint_eq_of_isOpenImmersion _

    have h2 : (Γ.fromSpecStalk γ).base (genericPoint (Spec (Γ.presheaf.stalk γ))) = genericPoint Γ := by
      obtain ⟨t, ht⟩ : genericPoint Γ ∈ Set.range (Γ.fromSpecStalk γ).base := by
        rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Γ).specializes trivial
      have hst : genericPoint (Spec (Γ.presheaf.stalk γ)) ⤳ t := (genericPoint_spec _).specializes trivial
      have h3 : (Γ.fromSpecStalk γ).base (genericPoint (Spec (Γ.presheaf.stalk γ))) ⤳ genericPoint Γ := by
        rw [← ht]; exact hst.map (Γ.fromSpecStalk γ).base.hom.continuous
      exact (h3.antisymm ((genericPoint_spec Γ).specializes trivial)).eq
    show (Spec.map (inv (π.stalkMap γ)) ≫ Γ.fromSpecStalk γ).base _ = _
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    erw [h1]
    exact h2

  obtain ⟨U, hηU, v, hv, hvw⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk sG sH (π.base γ) (w ≫ q)
      (by rw [Category.assoc, hπq, ← Category.assoc, hwπ])
  exact ⟨w, U, hηU, v, hwπ, hv, hvw, hwγ, hwξ⟩

theorem isOpenImmersion_SpecMap_algebraMap_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors R) ?_ ?_).mpr
      inferInstance
    · exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    · intro n hn
      obtain ⟨k, u, hk⟩ :=
        IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hn) hϖ
      refine ⟨ϖ ^ k, ⟨k, rfl⟩, ?_⟩
      rw [hk]
      exact (u.isUnit.mul_left_dvd).mpr dvd_rfl
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ

theorem nonempty_and_isIntegral_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) [IsIntegral G]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (hι : ι = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    [IsOpenImmersion ι]
    (η : G) (hη : g.base η = IsLocalRing.closedPoint R) (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk η)] :
    Nonempty ↥(pullback g ι) ∧ IsIntegral (pullback g ι) ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ Set.range (pullback.fst g ι).base) := by

  have hfib : ∀ x : G, g.base x ≠ IsLocalRing.closedPoint R →
      x ∈ Set.range (pullback.fst g ι).base := by
    intro x hx
    have hbot : (g.base x).asIdeal = ⊥ := by
      by_contra hne
      apply hx
      have hmax : (g.base x).asIdeal.IsMaximal := IsPrime.to_maximal_ideal hne
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, Set.mem_range]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    subst hι
    apply PrimeSpectrum.ext
    rw [hbot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

  have hξ : g.base (genericPoint G) ≠ IsLocalRing.closedPoint R := by
    intro hc
    have h1 : η ⤳ genericPoint G := hirr _ hc
    have h2 : genericPoint G ⤳ η := (genericPoint_spec G).specializes trivial
    have heq : η = genericPoint G := (h1.antisymm h2).eq
    apply IsDiscreteValuationRing.not_isField (G.presheaf.stalk η)
    rw [heq]
    exact Field.toIsField G.functionField
  obtain ⟨z, hz⟩ := hfib _ hξ
  haveI : Nonempty ↥(pullback g ι) := ⟨z⟩
  exact ⟨⟨z⟩, isIntegral_of_isOpenImmersion (pullback.fst g ι), hfib⟩
end AlgebraicGeometry.HeckeExt

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift IsImmersion.of_comp Scheme.fromSpecStalk_closedPoint Scheme.Hom.isoOpensRange_inv_comp Scheme.Opens.range_ι Scheme.Hom IsOpenImmersion.of_isLocalization Scheme.SpecMap_stalkSpecializes_fromSpecStalk Scheme.range_fromSpecStalk QuasiCompact Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Scheme.Opens.fromSpecStalkOfMem_ι ext_of_isDominant_of_isSeparated IsOpenImmersion Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion isIntegral_of_isOpenImmersion IsReduced IsSeparated QuasiCompact.of_comp IsImmersion Spec.map_id Scheme.SpecMap_stalkMap_fromSpecStalk Spec_closedPoint IsDominant genericPoint_eq_bot_of_affine IsOpenImmersion.lift_uniq Scheme.Opens Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.Opens.iSupOpenCover isReduced_of_isOpenImmersion Scheme.Hom.toImage_imageι IsOpenImmersion.lift_fac Scheme.Cover Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint Scheme.exists_opens_extension_of_fromSpecStalk"
namespace HeckeExt
p2m_open "AlgebraicGeometry"

theorem specMap_stalkSpecializes_genericPoint_apply {G : Scheme.{u}} [IsIntegral G] (η : G)
    (hξη : genericPoint G ⤳ η) (p : Spec (G.presheaf.stalk (genericPoint G))) :
    (Spec.map (G.presheaf.stalkSpecializes hξη)).base p = genericPoint (Spec (G.presheaf.stalk η)) := by
  rw [genericPoint_eq_bot_of_affine]
  have hinj : Function.Injective (G.presheaf.stalkSpecializes hξη).hom :=
    IsFractionRing.injective (G.presheaf.stalk η) G.functionField
  have hp : p = (⊥ : PrimeSpectrum (G.presheaf.stalk (genericPoint G))) :=
    @Subsingleton.elim (PrimeSpectrum (G.presheaf.stalk (genericPoint G))) inferInstance _ _
  subst hp
  apply PrimeSpectrum.ext
  change Ideal.comap (G.presheaf.stalkSpecializes hξη).hom ⊥ = ⊥
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

theorem glue_of_agree_on_pullback {G H S GK : Scheme.{u}} (g : G ⟶ S) (h : H ⟶ S)
    (U : G.Opens) (vU : (U : Scheme.{u}) ⟶ H) (hvU : vU ≫ h = U.ι ≫ g)
    (j : GK ⟶ G) [IsOpenImmersion j] (φ : GK ⟶ H) (hφ : φ ≫ h = j ≫ g)
    (hagree : pullback.fst U.ι j ≫ vU = pullback.snd U.ι j ≫ φ) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H), v ≫ h = V.ι ≫ g ∧ j.opensRange ≤ V ∧ U ≤ V ∧
      (∃ hle : Set.range j.base ⊆ Set.range V.ι.base, IsOpenImmersion.lift V.ι j hle ≫ v = φ) ∧
      (∃ hUV : U ≤ V, G.homOfLE hUV ≫ v = vU) := by

  let φ' : (j.opensRange : Scheme.{u}) ⟶ H := j.isoOpensRange.inv ≫ φ

  have cross : ∀ {T : Scheme.{u}} (a : T ⟶ U) (a' : T ⟶ j.opensRange),
      a ≫ U.ι = a' ≫ j.opensRange.ι → a ≫ vU = a' ≫ φ' := by
    intro T a a' e
    have e' : a ≫ U.ι = (a' ≫ j.isoOpensRange.inv) ≫ j := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]; exact e
    have h1 := pullback.lift_fst a (a' ≫ j.isoOpensRange.inv) e'
    have h2 := pullback.lift_snd a (a' ≫ j.isoOpensRange.inv) e'
    show a ≫ vU = a' ≫ (j.isoOpensRange.inv ≫ φ)
    rw [← h1, Category.assoc, hagree, ← Category.assoc, h2, Category.assoc]

  let W : Bool → G.Opens := fun b => bif b then U else j.opensRange
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  have hWι : ∀ b : Bool, 𝒰.f b ≫ (⨆ b, W b).ι = (W b).ι := fun b => G.homOfLE_ι (le_iSup W b)
  let fam : ∀ b : Bool, 𝒰.X b ⟶ H := fun b =>
    match b with
    | true => vU
    | false => φ'

  have hkey : ∀ (b c : Bool) {T : Scheme.{u}} (a : T ⟶ 𝒰.X b) (a' : T ⟶ 𝒰.X c),
      a ≫ 𝒰.f b ≫ (⨆ b, W b).ι = a' ≫ 𝒰.f c ≫ (⨆ b, W b).ι → a ≫ fam b = a' ≫ fam c := by
    rintro (_ | _) (_ | _) T a a' e
    ·
      have : a = a' := (cancel_mono (𝒰.f false ≫ (⨆ b, W b).ι)).mp e
      subst this; rfl
    ·
      have e' : a' ≫ U.ι = a ≫ j.opensRange.ι := by
        have e2 := e.symm
        rw [hWι true, hWι false] at e2
        exact e2
      exact (cross a' a e').symm
    ·
      have e' : a ≫ U.ι = a' ≫ j.opensRange.ι := by
        have e2 := e
        rw [hWι true, hWι false] at e2
        exact e2
      exact cross a a' e'
    ·
      have : a = a' := (cancel_mono (𝒰.f true ≫ (⨆ b, W b).ι)).mp e
      subst this; rfl
  have hf : ∀ b c : Bool, pullback.fst (𝒰.f b) (𝒰.f c) ≫ fam b = pullback.snd _ _ ≫ fam c := by
    intro b c
    apply hkey
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  have hfam : ∀ b : Bool, fam b ≫ h = 𝒰.f b ≫ (⨆ b, W b).ι ≫ g := by
    intro b
    rw [← Category.assoc, hWι b]
    cases b
    · show (j.isoOpensRange.inv ≫ φ) ≫ h = j.opensRange.ι ≫ g
      rw [Category.assoc, hφ, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    · exact hvU

  let v : ((⨆ b, W b : G.Opens) : Scheme.{u}) ⟶ H := 𝒰.glueMorphisms fam hf
  have hv : ∀ b, 𝒰.f b ≫ v = fam b := fun b => Scheme.Cover.ι_glueMorphisms 𝒰 fam hf b
  have hKV : j.opensRange ≤ ⨆ b, W b := le_iSup W false
  have hUV : U ≤ ⨆ b, W b := le_iSup W true
  refine ⟨⨆ b, W b, v, ?_, hKV, hUV, ?_, ⟨hUV, hv true⟩⟩
  ·
    apply Scheme.Cover.hom_ext 𝒰
    intro b
    rw [← Category.assoc, hv b]
    exact hfam b
  ·
    have hle : Set.range j.base ⊆ Set.range (⨆ b, W b).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hKV ⟨x, rfl⟩
    refine ⟨hle, ?_⟩
    have hlift : IsOpenImmersion.lift (⨆ b, W b).ι j hle = j.isoOpensRange.hom ≫ 𝒰.f false := by
      symm
      apply IsOpenImmersion.lift_uniq
      rw [Category.assoc]
      exact (congrArg (j.isoOpensRange.hom ≫ ·) (hWι false)).trans j.isoOpensRange_hom_ι
    rw [hlift, Category.assoc]
    exact (congrArg (j.isoOpensRange.hom ≫ ·) (hv false)).trans
      (Iso.hom_inv_id_assoc j.isoOpensRange φ)

theorem stepF {G H Γ GK S : Scheme.{u}} (g : G ⟶ S) (h : H ⟶ S) [IsIntegral G] [IsSeparated h]
    (j : GK ⟶ G) [IsOpenImmersion j]
    (φ : GK ⟶ H) (hφ : φ ≫ h = j ≫ g)
    (t : GK ⟶ Γ) [IsOpenImmersion t]
    (π : Γ ⟶ G) (q : Γ ⟶ H) (htπ : t ≫ π = j) (htq : t ≫ q = φ)
    (η : G) (U : G.Opens) (hηU : η ∈ U) (vU : (U : Scheme.{u}) ⟶ H) (hvU : vU ≫ h = U.ι ≫ g)
    (w : Spec (G.presheaf.stalk η) ⟶ Γ) (hwπ : w ≫ π = G.fromSpecStalk η)
    (hvUw : U.fromSpecStalkOfMem η hηU ≫ vU = w ≫ q)
    (hwgen : w.base (genericPoint (Spec (G.presheaf.stalk η))) ∈ Set.range t.base) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H), v ≫ h = V.ι ≫ g ∧ j.opensRange ≤ V ∧ η ∈ V ∧
      ∃ hle : Set.range j.base ⊆ Set.range V.ι.base, IsOpenImmersion.lift V.ι j hle ≫ v = φ := by
  classical
  have hξη : genericPoint G ⤳ η := (genericPoint_spec G).specializes (Set.mem_univ η)

  have hξU : genericPoint G ∈ U :=
    ((genericPoint_spec G).mem_open_set_iff U.isOpen).mpr ⟨η, Set.mem_univ _, hηU⟩
  have hξW : genericPoint G ∈ j.opensRange := by
    obtain ⟨z, _⟩ := hwgen
    exact ((genericPoint_spec G).mem_open_set_iff j.opensRange.isOpen).mpr
      ⟨j.base z, Set.mem_univ _, ⟨z, rfl⟩⟩
  have hrangeξ : Set.range (G.fromSpecStalk (genericPoint G)).base = {genericPoint G} := by
    rw [Scheme.range_fromSpecStalk]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun hy => (hy.antisymm ((genericPoint_spec G).specializes (Set.mem_univ y))).eq,
      fun hy => hy ▸ le_rfl⟩

  let τ : Spec (G.presheaf.stalk (genericPoint G)) ⟶ GK :=
    IsOpenImmersion.lift j (G.fromSpecStalk (genericPoint G)) (by
      rw [hrangeξ, Set.singleton_subset_iff]; exact hξW)
  have hτ : τ ≫ j = G.fromSpecStalk (genericPoint G) := IsOpenImmersion.lift_fac _ _ _
  let sU : Spec (G.presheaf.stalk (genericPoint G)) ⟶ (U : Scheme.{u}) :=
    IsOpenImmersion.lift U.ι (G.fromSpecStalk (genericPoint G)) (by
      rw [hrangeξ, Set.singleton_subset_iff, Scheme.Opens.range_ι]; exact hξU)
  have hsU : sU ≫ U.ι = G.fromSpecStalk (genericPoint G) := IsOpenImmersion.lift_fac _ _ _
  have hsU' : sU = Spec.map (G.presheaf.stalkSpecializes hξη) ≫ U.fromSpecStalkOfMem η hηU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hsU

  have hcore : Spec.map (G.presheaf.stalkSpecializes hξη) ≫ w = τ ≫ t := by
    have hr : Set.range (Spec.map (G.presheaf.stalkSpecializes hξη) ≫ w).base ⊆ Set.range t.base := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_base, TopCat.comp_app, specMap_stalkSpecializes_genericPoint_apply η hξη p]
      exact hwgen
    have h1 : IsOpenImmersion.lift t _ hr = τ := by
      rw [← cancel_mono j, hτ, ← htπ, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hwπ,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [← h1, IsOpenImmersion.lift_fac]

  have hagree : pullback.fst U.ι j ≫ vU = pullback.snd U.ι j ≫ φ := by
    let sP : Spec (G.presheaf.stalk (genericPoint G)) ⟶ pullback U.ι j :=
      pullback.lift sU τ (by rw [hsU, hτ])
    haveI : IsReduced (pullback U.ι j) := isReduced_of_isOpenImmersion (pullback.fst U.ι j)
    haveI : IsDominant sP := by
      let e : pullback U.ι j ⟶ G := pullback.fst U.ι j ≫ U.ι
      have he1 : sP ≫ e = G.fromSpecStalk (genericPoint G) := by
        simp only [sP, e, pullback.lift_fst_assoc, hsU]
      have he2 : e.base (sP.base (IsLocalRing.closedPoint _)) = genericPoint G := by
        rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, he1]
        exact Scheme.fromSpecStalk_closedPoint
      have hd : Dense ({sP.base (IsLocalRing.closedPoint _)} : Set ↥(pullback U.ι j)) := by
        rw [dense_iff_closure_eq, e.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
          Set.image_singleton, he2]
        rw [show closure ({genericPoint G} : Set G) = Set.univ from genericPoint_closure G]
        simp
      exact ⟨hd.mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)⟩
    refine ext_of_isDominant_of_isSeparated h ?_ sP ?_
    · rw [Category.assoc, Category.assoc, hvU, hφ, pullback.condition_assoc]
    · simp only [sP, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      rw [hsU', Category.assoc, hvUw, ← Category.assoc, hcore, Category.assoc, htq]

  obtain ⟨V, v, hv, hWV, hUV, ⟨hle, hlift⟩, -⟩ := glue_of_agree_on_pullback g h U vU hvU j φ hφ hagree
  exact ⟨V, v, hv, hWV, hUV hηU, hle, hlift⟩

end AlgebraicGeometry.HeckeExt

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift IsImmersion.of_comp Scheme.fromSpecStalk_closedPoint Scheme.Hom.isoOpensRange_inv_comp Scheme.Opens.range_ι Scheme.Hom IsOpenImmersion.of_isLocalization Scheme.SpecMap_stalkSpecializes_fromSpecStalk Scheme.range_fromSpecStalk QuasiCompact Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Scheme.Opens.fromSpecStalkOfMem_ι ext_of_isDominant_of_isSeparated IsOpenImmersion Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion isIntegral_of_isOpenImmersion IsReduced IsSeparated QuasiCompact.of_comp IsImmersion Spec.map_id Scheme.SpecMap_stalkMap_fromSpecStalk Spec_closedPoint IsDominant genericPoint_eq_bot_of_affine IsOpenImmersion.lift_uniq Scheme.Opens Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext Scheme.Opens.iSupOpenCover isReduced_of_isOpenImmersion Scheme.Hom.toImage_imageι IsOpenImmersion.lift_fac Scheme.Cover Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint Scheme.exists_opens_extension_of_fromSpecStalk"
namespace HeckeExt
p2m_open "AlgebraicGeometry"

open AlgebraicGeometry.HeckeExt in

theorem exists_opens_extension_of_mem_image_graph_aux
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
    [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (hι : ι = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (φK : pullback g ι ⟶ pullback h ι) (hφK : φK ≫ pullback.snd h ι = pullback.snd g ι)
    (graph : pullback g ι ⟶ pullback g h)
    (hgraph_fst : graph ≫ pullback.fst g h = pullback.fst g ι)
    (hgraph_snd : graph ≫ pullback.snd g h = φK ≫ pullback.fst h ι)
    (γ : ↥(graph.image))
    (hη : g.base ((graph.imageι ≫ pullback.fst g h).base γ) = IsLocalRing.closedPoint R)
    (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → (graph.imageι ≫ pullback.fst g h).base γ ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk ((graph.imageι ≫ pullback.fst g h).base γ))] :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (graph.imageι ≫ pullback.fst g h).base γ ∈ V ∧
      ∃ hle : Set.range (pullback.fst g ι).base ⊆ Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g ι) hle ≫ v = φK ≫ pullback.fst h ι := by
  set η := (graph.imageι ≫ pullback.fst g h).base γ with hηdef
  set π : graph.image ⟶ G := graph.imageι ≫ pullback.fst g h with hπdef
  set q : graph.image ⟶ H := graph.imageι ≫ pullback.snd g h with hqdef
  have hπq : q ≫ h = π ≫ g := by
    simp only [hπdef, hqdef, Category.assoc, pullback.condition]

  haveI hιopen : IsOpenImmersion ι := hι ▸ isOpenImmersion_SpecMap_algebraMap_of_isDiscreteValuationRing R K
  haveI : QuasiCompact graph := by
    have : QuasiCompact (graph ≫ pullback.fst g h) := by rw [hgraph_fst]; infer_instance
    exact QuasiCompact.of_comp graph (pullback.fst g h)
  haveI : IsImmersion graph := by
    have : IsImmersion (graph ≫ pullback.fst g h) := by rw [hgraph_fst]; infer_instance
    exact IsImmersion.of_comp graph (pullback.fst g h)
  obtain ⟨hGKne, hGKint, hrange⟩ := nonempty_and_isIntegral_genericFibre g ι hι η hη hirr
  haveI := hGKne; haveI := hGKint

  obtain ⟨hΓint, hπgen, hπbir, htoIm⟩ :=
    isIntegral_image_and_birational graph (pullback.fst g h) (pullback.fst g ι) hgraph_fst
  haveI := hΓint

  obtain ⟨w, U, hηU, vU, hwπ, hvU, hvUw, hwγ, hwgen⟩ :=
    exists_opens_extension_near_of_birational π q g h hπq hπgen hπbir γ

  have htπ : graph.toImage ≫ π = pullback.fst g ι := by
    rw [hπdef, ← Category.assoc, Scheme.Hom.toImage_imageι, hgraph_fst]
  have htq : graph.toImage ≫ q = φK ≫ pullback.fst h ι := by
    rw [hqdef, ← Category.assoc, Scheme.Hom.toImage_imageι, hgraph_snd]
  have hφ : (φK ≫ pullback.fst h ι) ≫ h = pullback.fst g ι ≫ g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hφK, pullback.condition]
  have hwgen' : w.base (genericPoint (Spec (G.presheaf.stalk η))) ∈ Set.range graph.toImage.base :=
    ⟨genericPoint _, by rw [htoIm, hwgen]⟩
  obtain ⟨V, v, hv, hKV, hηV, hle, hlift⟩ :=
    stepF g h (pullback.fst g ι) (φK ≫ pullback.fst h ι) hφ graph.toImage π q htπ htq η U hηU vU hvU
      w hwπ hvUw hwgen'
  refine ⟨V, v, hv, ?_, hηV, hle, hlift⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hrange x hx
  exact hKV ⟨y, rfl⟩

end AlgebraicGeometry.HeckeExt

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
    [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (η : G) (hη : g.base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk η)]
    (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hφK : φK ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (γ : ↥((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).image))
    (hγ : ((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).imageι ≫
          pullback.fst g h).base γ = η) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆
          Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
          φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  subst hγ
  exact AlgebraicGeometry.HeckeExt.exists_opens_extension_of_mem_image_graph_aux K g h _ rfl φK hφK _
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) γ hη hirr

end S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph (solution)
