-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.IsSymmetric.of_forall_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/169a43ef-3101-56fe-add7-ccbfcb3f56ae

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_IsSymmetric_of_forall_away

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

namespace T3Z2A

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def pbCompObj {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  ((pullbackComp f g).symm).app M

theorem locIsoOnBase_of_forall_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (M N : A.Modules)
    (hloc : ∀ i, LocIsoOnBase (f' i) ((Scheme.Modules.pullback (g i)).obj M) ((Scheme.Modules.pullback (g i)).obj N)) :
    LocIsoOnBase f M N := by
  classical
  have hcovS : ∀ p : ↥(Spec (CommRingCat.of S)), ∃ i y,
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))).base y = p := by
    intro p
    have htop : (⨆ i, PrimeSpectrum.basicOpen (r i)) = ⊤ := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hr
    have hp : p ∈ (⨆ i, PrimeSpectrum.basicOpen (r i) : TopologicalSpace.Opens _) := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    have hrg : Set.range (fun y => (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))).base y) =
        ((PrimeSpectrum.basicOpen (r i) : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)]; rfl
    have hi' : p ∈ Set.range (fun y => (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))).base y) := by
      rw [hrg]; exact hi
    obtain ⟨y, hy⟩ := hi'
    exact ⟨i, y, hy⟩
  intro s
  obtain ⟨i, y, hy⟩ := hcovS s
  obtain ⟨U', hyU', ⟨η⟩⟩ := hloc i y
  haveI : IsOpenImmersion (g i) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hg i).flip inferInstance
  let ιi := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))
  let U : (Spec (CommRingCat.of S)).Opens := ⟨ιi.base '' (U' : Set _), ιi.isOpenEmbedding.isOpenMap _ U'.2⟩
  refine ⟨U, ⟨y, hyU', hy⟩, ?_⟩
  have hrg : Set.range (g i).base = f.base ⁻¹' Set.range ιi.base := by
    rw [show g i = (hg i).isoPullback.hom ≫ pullback.fst _ _ from ((hg i).isoPullback_hom_fst).symm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ,
      Scheme.Pullback.range_fst]
    exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (hg i).isoPullback)).surjective
  have hinj : Function.Injective ιi.base := ιi.isOpenEmbedding.injective
  have hgw : ∀ z, f.base ((g i).base z) = ιi.base ((f' i).base z) := fun z => by
    have := congrArg (fun φ => φ.base z) (hg i).w
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this
  have hrange : Set.range (((f' i) ⁻¹ᵁ U').ι ≫ g i).base = Set.range (f ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(f' i).base z, hz, (hgw z).symm⟩
    · rintro ⟨y', hy', hx⟩
      have : x ∈ Set.range (g i).base := by rw [hrg]; exact ⟨y', hx⟩
      obtain ⟨z, rfl⟩ := this
      refine ⟨z, ?_, rfl⟩
      show (f' i).base z ∈ (U' : Set _)
      have : ιi.base ((f' i).base z) = ιi.base y' := by rw [← hgw z]; exact hx.symm
      rwa [hinj this]
  let θ := IsOpenImmersion.isoOfRangeEq (((f' i) ⁻¹ᵁ U').ι ≫ g i) (f ⁻¹ᵁ U).ι hrange
  have hθ : θ.inv ≫ ((f' i) ⁻¹ᵁ U').ι ≫ g i = (f ⁻¹ᵁ U).ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have T := fun (P : A.Modules) =>
    (Scheme.Modules.pullbackCongr hθ.symm).app P ≪≫ pbCompObj θ.inv (((f' i) ⁻¹ᵁ U').ι ≫ g i) P ≪≫
      (Scheme.Modules.pullback θ.inv).mapIso (pbCompObj ((f' i) ⁻¹ᵁ U').ι (g i) P)
  exact ⟨T M ≪≫ (Scheme.Modules.pullback θ.inv).mapIso η ≪≫ (T N).symm⟩

end T3Z2A

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (L' : ∀ i, RelativeGroupLaw (Localization.Away (r i)) (f' i))
    (hL' : ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (x y : SchemeHomOver t' (f' i)),
      ((L' i).mul t' x y).1 ≫ g i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    (𝓛 : A.Modules)
    (hloc : ∀ i, IsSymmetric (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛)) :
    IsSymmetric f L 𝓛 := by
  classical

  have hneg : ∀ i, negMor (f' i) (L' i) ≫ g i = g i ≫ negMor f L := by
    intro i
    have hgw : g i ≫ f = f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) := (hg i).w
    letI G0 : Group (SchemeHomOver f f) := L.pointGroup f
    letI G' : Group (SchemeHomOver (f' i) (f' i)) := (L' i).pointGroup (f' i)
    letI G : Group (SchemeHomOver (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) f) :=
      L.pointGroup _

    let φ : SchemeHomOver (f' i) (f' i) →
        SchemeHomOver (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) f :=
      fun x => ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
    have hφ : ∀ x y, φ (x * y) = φ x * φ y := fun x y => Subtype.ext (hL' i (f' i) x y)
    let Φ : SchemeHomOver (f' i) (f' i) →*
        SchemeHomOver (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) f := MonoidHom.mk' φ hφ

    let Ψ : SchemeHomOver f f →*
        SchemeHomOver (f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))) f :=
      MonoidHom.mk' (schemeHomOverComp (g i) hgw) (L.mul_natural f _ (g i) hgw)
    have h1 : Φ ((L' i).inv (f' i) (idPt (f' i))) = (Φ (idPt (f' i)))⁻¹ := Φ.map_inv _
    have h2 : Ψ (L.inv f (idPt f)) = (Ψ (idPt f))⁻¹ := Ψ.map_inv _
    have h3 : Φ (idPt (f' i)) = Ψ (idPt f) := by
      apply Subtype.ext
      show 𝟙 _ ≫ g i = g i ≫ 𝟙 _
      simp
    have h4 : Φ ((L' i).inv (f' i) (idPt (f' i))) = Ψ (L.inv f (idPt f)) := by rw [h1, h2, h3]
    exact congrArg Subtype.val h4

  refine T3Z2A.locIsoOnBase_of_forall_away f r hr A' f' g hg _ _ fun i => ?_
  have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (f' i)
  refine E.trans (fun s => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso ?_⟩⟩) (hloc i)
  exact (T3Z2A.pbCompObj (g i) (negMor f L) 𝓛).symm ≪≫ (Scheme.Modules.pullbackCongr (hneg i).symm).app 𝓛 ≪≫
    T3Z2A.pbCompObj (negMor (f' i) (L' i)) (g i) 𝓛

end S_AlgebraicGeometry_Polarisation_IsSymmetric_of_forall_away
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_IsSymmetric_of_forall_away (solution)
