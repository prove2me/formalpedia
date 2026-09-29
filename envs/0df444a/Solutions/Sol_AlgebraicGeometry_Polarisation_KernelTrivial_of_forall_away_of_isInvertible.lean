-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.KernelTrivial.of_forall_away_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/747126d4-685b-5deb-b816-e0f90b456d90

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace E24KTLOC

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

theorem one_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of S)} (hs : s = s') :
    (L.one s).1 = (L.one s').1 := by
  subst hs; rfl

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

end E24KTLOC
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible.E24KTLOC"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible.E24KTLOC"

open E24KTLOC in

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
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hloc : ∀ i, KernelTrivial (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛)) :
    KernelTrivial f L 𝓛 := by
  classical
  intro R _ t x H

  let ι : ∀ i, Spec (CommRingCat.of (Localization.Away (r i))) ⟶ Spec (CommRingCat.of S) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))
  have hw : ∀ i, g i ≫ f = f' i ≫ ι i := fun i => (hg i).w
  have hom : ∀ (i : Fin k) (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (P Q : SchemeHomOver t' (f' i)),
      ((L' i).mul t' P Q).1 ≫ g i =
        (L.mul (t' ≫ ι i)
          ⟨P.1 ≫ g i, by rw [Category.assoc, hw i, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g i, by rw [Category.assoc, hw i, ← Category.assoc, Q.2]⟩).1 :=
    fun i T t' P Q => hL' i t' P Q
  have hmono : ∀ i, Mono (g i) := fun i =>
    haveI : IsOpenImmersion (g i) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hg i).flip inferInstance
    inferInstance

  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* R, Spec.map (CommRingCat.ofHom φ) = t :=
    ⟨(Spec.preimage t).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩

  let s : Fin k → R := fun i => φ (r i)
  have hs : Ideal.span (Set.range s) = ⊤ := by
    have hsr : Set.range s = φ '' Set.range r := Set.range_comp φ r
    rw [hsr, ← Ideal.map_span φ, hr, Ideal.map_top]
  let u : ∀ i, Spec (CommRingCat.of (Localization.Away (s i))) ⟶ Spec (CommRingCat.of R) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  let ψ : ∀ i, Localization.Away (r i) →+* Localization.Away (s i) := fun i => Localization.awayMap φ (r i)
  let t' : ∀ i, Spec (CommRingCat.of (Localization.Away (s i))) ⟶ Spec (CommRingCat.of (Localization.Away (r i))) :=
    fun i => Spec.map (CommRingCat.ofHom (ψ i))
  have hbase : ∀ i, t' i ≫ ι i = u i ≫ t := by
    intro i
    have hc : (ψ i).comp (algebraMap S (Localization.Away (r i))) = (algebraMap R (Localization.Away (s i))).comp φ := by
      ext a
      simp [s, ψ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    calc t' i ≫ ι i = Spec.map (CommRingCat.ofHom ((ψ i).comp (algebraMap S (Localization.Away (r i))))) := by
          rw [CommRingCat.ofHom_comp, Spec.map_comp]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away (s i))).comp φ)) := by rw [hc]
      _ = u i ≫ t := by rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ]

  have hxt : ∀ i, (u i ≫ x.1) ≫ f = t' i ≫ ι i := fun i => by rw [Category.assoc, x.2, hbase]
  let x' : ∀ i, SchemeHomOver (t' i) (f' i) := fun i =>
    ⟨(hg i).lift (u i ≫ x.1) (t' i) (hxt i), (hg i).lift_snd _ _ _⟩
  have hx' : ∀ i, (x' i).1 ≫ g i = u i ≫ x.1 := fun i => (hg i).lift_fst _ _ _

  have hRHS : ∀ i, x' i = (L' i).one (t' i) → u i ≫ x.1 = u i ≫ (L.one t).1 := by
    intro i hi
    have ho : u i ≫ (L.one t).1 = (L.one (u i ≫ t)).1 :=
      congrArg Subtype.val (L.one_natural t (u i ≫ t) (u i) rfl)
    have eO : ((L' i).one (t' i)).1 ≫ g i = (L.one (u i ≫ t)).1 := by
      rw [one_val_comp L (L' i) (ι i) (g i) (hw i) (hom i) (t' i)]
      exact one_val_congr L (hbase i)
    rw [← hx' i, hi, eO, ho]

  let j : ∀ i, pullback (f' i) (t' i) ⟶ pullback f t := fun i =>
    pullback.lift (pullback.fst (f' i) (t' i) ≫ g i) (pullback.snd (f' i) (t' i) ≫ u i)
      (by rw [Category.assoc, Category.assoc, hw i, ← hbase i, pullback.condition_assoc])
  have hj1 : ∀ i, j i ≫ pullback.fst f t = pullback.fst (f' i) (t' i) ≫ g i := fun i => pullback.lift_fst _ _ _
  have hj2 : ∀ i, j i ≫ pullback.snd f t = pullback.snd (f' i) (t' i) ≫ u i := fun i => pullback.lift_snd _ _ _
  have hjc : ∀ i, IsPullback (j i) (pullback.snd (f' i) (t' i)) (pullback.snd f t) (u i) := fun i =>
    isPullback_of_lift (hg i) (t' i) t (u i) (hbase i) (j i) (hj1 i) (hj2 i)
  let pp : ∀ i, pullback (f' i) (f' i) ⟶ pullback f f :=
    fun i => pullback.map (f' i) (f' i) f f (g i) (g i) (ι i) (hw i).symm (hw i).symm

  have hslice : ∀ i, j i ≫ sliceAt f x = sliceAt (f' i) (x' i) ≫ pp i := by
    intro i
    apply pullback.hom_ext
    · simp only [sliceAt, j, pp, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [sliceAt, j, pp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hx']

  have hK : ∀ i, Nonempty ((Scheme.Modules.pullback (j i)).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt (f' i) (x' i))).obj
        (mumfordBundle (f' i) (L' i) ((Scheme.Modules.pullback (g i)).obj 𝓛))) := by
    intro i
    obtain ⟨ΛIso⟩ := nonempty_mumfordBundleIso L (L' i) (ι i) (g i) (hw i) (hom i) 𝓛 h𝓛
    exact ⟨(Scheme.Modules.pullbackComp (j i) (sliceAt f x)).app _ ≪≫ (Scheme.Modules.pullbackCongr (hslice i)).app _ ≪≫
      ((Scheme.Modules.pullbackComp (sliceAt (f' i) (x' i)) (pp i)).app _).symm ≪≫
      (Scheme.Modules.pullback (sliceAt (f' i) (x' i))).mapIso ΛIso.symm⟩

  apply Subtype.ext
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) s hs).openCover.hom_ext _ _ fun i => ?_
  change u i ≫ x.1 = u i ≫ (L.one t).1
  refine hRHS i (hloc i (Localization.Away (s i)) (t' i) (x' i) ?_)
  have H1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd (f' i) (t' i)) (j i) (u i) (hj2 i) H
  obtain ⟨K⟩ := hK i
  have E := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd (f' i) (t' i))
  exact E.trans (locIsoOnBase_of_iso _ K.symm)
    (E.trans H1 (locIsoOnBase_of_iso _ (Scheme.Modules.pullbackTensorUnitObjIso (j i))))

end S_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_KernelTrivial_of_forall_away_of_isInvertible (solution)
