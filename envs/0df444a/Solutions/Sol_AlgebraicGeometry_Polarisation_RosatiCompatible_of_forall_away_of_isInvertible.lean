-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.RosatiCompatible.of_forall_away_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1a1c7d20-fdf5-5564-9f41-5c0a37adf62b

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_of_forall_away_of_isInvertible

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace R2Z2b

theorem isPullback_of_lift {C : Type*} [Category C] {A A' B B' T T₁ : C} {f : A ⟶ B} {f' : A' ⟶ B'} {gA : A' ⟶ A}
    {b : B' ⟶ B} (hg : IsPullback gA f' f b) (ι'' : T ⟶ B') (ι₁ : T₁ ⟶ B) (j : T ⟶ T₁) (hbase : ι'' ≫ b = j ≫ ι₁)
    [HasPullback f' ι''] [HasPullback f ι₁]
    (u₁ : pullback f' ι'' ⟶ pullback f ι₁) (h1 : u₁ ≫ pullback.fst f ι₁ = pullback.fst f' ι'' ≫ gA)
    (h2 : u₁ ≫ pullback.snd f ι₁ = pullback.snd f' ι'' ≫ j) :
    IsPullback u₁ (pullback.snd f' ι'') (pullback.snd f ι₁) j := by
  have big := (IsPullback.of_hasPullback f' ι'').paste_horiz hg
  rw [← h1, hbase] at big
  exact IsPullback.of_right big h2 (IsPullback.of_hasPullback f ι₁)

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem inv_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s')
    (P : SchemeHomOver s f) (Q : SchemeHomOver s' f) (hPQ : P.1 = Q.1) : (L.inv s P).1 = (L.inv s' Q).1 := by
  subst hs; cases Subtype.ext hPQ; rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

def transitionHom (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') :
    letI := G.pointGroup t; letI := G.pointGroup t''; SchemeHomOver t f →* SchemeHomOver t'' f :=
  letI := G.pointGroup t; letI := G.pointGroup t''
  { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
    map_one' := G.one_natural t t'' ψ hψ
    map_mul' := fun x y => G.mul_natural t t'' ψ hψ x y }

theorem inv_natural (G : RelativeGroupLaw S f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (t'' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t'' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t''
  exact map_inv (transitionHom G t t'' ψ hψ) x

variable {S' : Type u} [CommRing S'] {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')}

def pushAlong (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ ψ) f :=
  ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩

@[scoped simp] theorem pushAlong_val (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A)
    (hu : u ≫ f = f' ≫ ψ) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    (pushAlong ψ u hu t' P).1 = P.1 ≫ u := rfl

section Hom

variable (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
  (ψ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (u : A' ⟶ A) (hu : u ≫ f = f' ≫ ψ)
  (hom : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ u =
      (L.mul (t' ≫ ψ)
        ⟨P.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ u, by rw [Category.assoc, hu, ← Category.assoc, Q.2]⟩).1)

def pushHom {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ ψ)
    SchemeHomOver t' f' →* SchemeHomOver (t' ≫ ψ) f :=
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  MonoidHom.mk' (fun P => pushAlong ψ u hu t' P) (fun P Q => Subtype.ext (hom T t' P Q))

include hom in
theorem pushAlong_mul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.mul t' P Q) = L.mul (t' ≫ ψ) (pushAlong ψ u hu t' P) (pushAlong ψ u hu t' Q) :=
  Subtype.ext (hom T t' P Q)

include hom in
theorem pushAlong_one {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    pushAlong ψ u hu t' (L'.one t') = L.one (t' ≫ ψ) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_one (pushHom L L' ψ u hu hom t')

include hom in
theorem pushAlong_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f') :
    pushAlong ψ u hu t' (L'.inv t' P) = L.inv (t' ≫ ψ) (pushAlong ψ u hu t' P) := by
  letI := L'.pointGroup t'
  letI := L.pointGroup (t' ≫ ψ)
  exact map_inv (pushHom L L' ψ u hu hom t') P

include hom in

theorem one_val_comp {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ u = (L.one (t' ≫ ψ)).1 :=
  congrArg Subtype.val (pushAlong_one L L' ψ u hu hom t')

include hom in

theorem negMor_comp : negMor f' L' ≫ u = u ≫ negMor f L := by
  have h1 : negMor f' L' ≫ u = (L.inv _ (pushAlong ψ u hu f' (idPt f'))).1 := by
    change (pushAlong ψ u hu f' (L'.inv f' (idPt f'))).1 = _
    rw [pushAlong_inv L L' ψ u hu hom]
  have h2 : u ≫ negMor f L = (L.inv (u ≫ f) (GoodReductionJacobian.schemeHomOverComp u rfl (idPt f))).1 := by
    change (GoodReductionJacobian.schemeHomOverComp u rfl (L.inv f (idPt f))).1 = _
    rw [inv_natural]
  rw [h1, h2]
  exact inv_val_congr L hu.symm _ _ (by simp [idPt])

include hom in

theorem addMor_comp :
    addMor f' L' ≫ u = pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ addMor f L := by
  have lhs := hom _ (pullback.fst f' f' ≫ f') ⟨pullback.fst f' f', rfl⟩ ⟨pullback.snd f' f', pullback.condition.symm⟩
  have rhs := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.map f' f' f f u u ψ hu.symm hu.symm ≫ pullback.fst f f ≫ f)
      (pullback.map f' f' f f u u ψ hu.symm hu.symm) rfl ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
  rw [addMor, addMor, lhs, rhs]
  refine mul_val_congr L ?_ _ _ _ _ ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst_assoc, hu]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_snd]

include hom in
theorem nonempty_mumfordBundleIso (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.map f' f' f f u u ψ hu.symm hu.symm)).obj (mumfordBundle f L 𝓛)) := by
  let pp : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f u u ψ hu.symm hu.symm
  have hadd : addMor f' L' ≫ u = pp ≫ addMor f L := addMor_comp L L' ψ u hu hom
  have hfst : pullback.fst f' f' ≫ u = pp ≫ pullback.fst f f := by simp only [pp, pullback.lift_fst]
  have hsnd : pullback.snd f' f' ≫ u = pp ≫ pullback.snd f f := by simp only [pp, pullback.lift_snd]
  obtain ⟨D⟩ := hinv.pullback_dual_monoidalV2 u
  let J1 : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback u).obj 𝓛) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') u).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hadd).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp pp (addMor f L)).app 𝓛).symm
  let J2 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.fst f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.fst f f)).app _).symm
  let J3 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback u).obj 𝓛)) ≅
      (Scheme.Modules.pullback pp).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback (pullback.snd f' f')).mapIso D.symm ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f' f') u).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
        ((Scheme.Modules.pullbackComp pp (pullback.snd f f)).app _).symm
  exact ⟨(J1 ⊗ᵢ (J2 ⊗ᵢ J3)) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso pp _ _).symm ≪≫
      (Scheme.Modules.pullbackTensorObjIso pp _ _).symm⟩

end Hom

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

end R2Z2b
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_of_forall_away_of_isInvertible.R2Z2b"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_of_forall_away_of_isInvertible.R2Z2b"

open R2Z2b in
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
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (act' : ∀ i, I → (A' i ⟶ A' i)) (act_over' : ∀ (i : Fin k) (x : I), act' i x ≫ f' i = f' i)
    (hact' : ∀ (i : Fin k) (x : I), act' i x ≫ g i = g i ≫ act x)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hloc : ∀ i, RosatiCompatible (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛) (act' i) (act_over' i) star) :
    RosatiCompatible f L 𝓛 act act_over star := by
  classical
  intro b

  let ψ : ∀ i, Spec (CommRingCat.of (Localization.Away (r i))) ⟶ Spec (CommRingCat.of S) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))
  have hw : ∀ i, g i ≫ f = f' i ≫ ψ i := fun i => (hg i).w
  let pp : ∀ i, pullback (f' i) (f' i) ⟶ pullback f f :=
    fun i => pullback.map (f' i) (f' i) f f (g i) (g i) (ψ i) (hw i).symm (hw i).symm
  have hom : ∀ (i : Fin k) (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (P Q : SchemeHomOver t' (f' i)),
      ((L' i).mul t' P Q).1 ≫ g i =
        (L.mul (t' ≫ ψ i)
          ⟨P.1 ≫ g i, by rw [Category.assoc, hw i, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g i, by rw [Category.assoc, hw i, ← Category.assoc, Q.2]⟩).1 :=
    fun i T t' P Q => hL' i t' P Q

  let m : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ act b) (by rw [Category.assoc, act_over]; exact pullback.condition)
  let n : pullback f f ⟶ pullback f f :=
    pullback.lift (pullback.fst f f ≫ act (star b)) (pullback.snd f f)
      (by rw [Category.assoc, act_over]; exact pullback.condition)

  have hchart : ∀ i, LocIsoOnBase (pullback.fst (f' i) (f' i) ≫ f' i)
      ((Scheme.Modules.pullback (pp i)).obj ((Scheme.Modules.pullback m).obj (mumfordBundle f L 𝓛)))
      ((Scheme.Modules.pullback (pp i)).obj ((Scheme.Modules.pullback n).obj (mumfordBundle f L 𝓛))) := by
    intro i
    obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L (L' i) (ψ i) (g i) (hw i) (hom i) 𝓛 h𝓛
    let m' : pullback (f' i) (f' i) ⟶ pullback (f' i) (f' i) :=
      pullback.lift (pullback.fst (f' i) (f' i)) (pullback.snd (f' i) (f' i) ≫ act' i b)
        (by rw [Category.assoc, act_over']; exact pullback.condition)
    let n' : pullback (f' i) (f' i) ⟶ pullback (f' i) (f' i) :=
      pullback.lift (pullback.fst (f' i) (f' i) ≫ act' i (star b)) (pullback.snd (f' i) (f' i))
        (by rw [Category.assoc, act_over']; exact pullback.condition)
    have hm : m' ≫ pp i = pp i ≫ m := by
      apply pullback.hom_ext
      · simp only [m, m', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [m, m', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hact']
    have hn : n' ≫ pp i = pp i ≫ n := by
      apply pullback.hom_ext
      · simp only [n, n', pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hact']
      · simp only [n, n', pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    let Im : (Scheme.Modules.pullback m').obj (mumfordBundle (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛)) ≅
        (Scheme.Modules.pullback (pp i)).obj ((Scheme.Modules.pullback m).obj (mumfordBundle f L 𝓛)) :=
      (Scheme.Modules.pullback m').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp m' (pp i)).app _ ≪≫
        (Scheme.Modules.pullbackCongr hm).app _ ≪≫ ((Scheme.Modules.pullbackComp (pp i) m).app _).symm
    let In : (Scheme.Modules.pullback n').obj (mumfordBundle (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛)) ≅
        (Scheme.Modules.pullback (pp i)).obj ((Scheme.Modules.pullback n).obj (mumfordBundle f L 𝓛)) :=
      (Scheme.Modules.pullback n').mapIso ΛIso ≪≫ (Scheme.Modules.pullbackComp n' (pp i)).app _ ≪≫
        (Scheme.Modules.pullbackCongr hn).app _ ≪≫ ((Scheme.Modules.pullbackComp (pp i) n).app _).symm
    have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.fst (f' i) (f' i) ≫ f' i)
    exact E.trans (locIsoOnBase_of_iso _ Im.symm) (E.trans (hloc i b) (locIsoOnBase_of_iso _ In))

  have hpp : ∀ i, IsPullback (pp i) (pullback.fst (f' i) (f' i) ≫ f' i) (pullback.fst f f ≫ f) (ψ i) := by
    intro i
    have sq : IsPullback (pp i) (pullback.snd (f' i) (f' i)) (pullback.snd f f) (g i) :=
      isPullback_of_lift (hg i) (f' i) f (g i) (hw i).symm (pp i)
        (by simp only [pp, pullback.lift_fst]) (by simp only [pp, pullback.lift_snd])
    have big := sq.paste_vert (hg i)
    rw [← pullback.condition, ← pullback.condition] at big
    exact big
  exact R2Z2b.locIsoOnBase_of_forall_away (pullback.fst f f ≫ f) r hr (fun i => pullback (f' i) (f' i))
    (fun i => pullback.fst (f' i) (f' i) ≫ f' i) pp hpp _ _ hchart

end S_AlgebraicGeometry_Polarisation_RosatiCompatible_of_forall_away_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_RosatiCompatible_of_forall_away_of_isInvertible (solution)
