-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4e675ec8-af60-5498-89f6-5e42a4ad9f79

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace K2Iso

variable {S : Type u} [CommRing S]

def mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩

@[scoped simp] theorem mapPt_coe {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (P : SchemeHomOver t f) :
    (mapPt φ hφ P).1 = P.1 ≫ φ := rfl

theorem sliceAt_fst {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x : SchemeHomOver t f) : sliceAt f x ≫ pullback.fst f f = pullback.fst f t := by
  unfold sliceAt; exact pullback.lift_fst _ _ _

theorem sliceAt_snd {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x : SchemeHomOver t f) : sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
  unfold sliceAt; exact pullback.lift_snd _ _ _

def IsPtHom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
    (L.mul t x y).1 ≫ φ = (L'.mul t (mapPt φ hφ x) (mapPt φ hφ y)).1

theorem IsPtHom.inv {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    {L : RelativeGroupLaw S f} {L' : RelativeGroupLaw S f'} (e : A ≅ A') {he : e.hom ≫ f' = f}
    (h : IsPtHom L L' e.hom he) (hei : e.inv ≫ f = f') : IsPtHom L' L e.inv hei := by
  intro T t x y
  have h1 := h T t (mapPt e.inv hei x) (mapPt e.inv hei y)
  have ex : mapPt e.hom he (mapPt e.inv hei x) = x := Subtype.ext (by simp [mapPt_coe])
  have ey : mapPt e.hom he (mapPt e.inv hei y) = y := Subtype.ext (by simp [mapPt_coe])
  rw [ex, ey] at h1
  rw [← cancel_mono e.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h1.symm

theorem IsPtHom.one_map {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    {L : RelativeGroupLaw S f} {L' : RelativeGroupLaw S f'} {φ : A ⟶ A'} {hφ : φ ≫ f' = f}
    (h : IsPtHom L L' φ hφ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 ≫ φ = (L'.one t).1 := by
  letI := L.pointGroup t
  letI := L'.pointGroup t
  have hΦ : ∀ x y : SchemeHomOver t f, mapPt φ hφ (x * y) = mapPt φ hφ x * mapPt φ hφ y :=
    fun x y => Subtype.ext (h T t x y)
  exact congrArg Subtype.val (MonoidHom.mk' (mapPt φ hφ) hΦ).map_one

theorem locIso_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S'))
    {M M' : X.Modules} (i : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso i⟩⟩

theorem nonempty_mumfordBundle_iso_pullback
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hg : e.inv ≫ f = f') (hmul' : IsPtHom L' L e.inv hg)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛)
    (GG : pullback f' f' ⟶ pullback f f)
    (hGG1 : GG ≫ pullback.fst f f = pullback.fst f' f' ≫ e.inv)
    (hGG2 : GG ≫ pullback.snd f f = pullback.snd f' f' ≫ e.inv) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛) ≅
      (Scheme.Modules.pullback GG).obj (mumfordBundle f L 𝓛)) := by
  have hGGt : GG ≫ (pullback.fst f f ≫ f) = pullback.fst f' f' ≫ f' := by
    rw [← Category.assoc, hGG1, Category.assoc, hg]

  have hmG : addMor f' L' ≫ e.inv = GG ≫ addMor f L := by
    let P₁' : SchemeHomOver (pullback.fst f' f' ≫ f') f' := ⟨pullback.fst f' f', rfl⟩
    let P₂' : SchemeHomOver (pullback.fst f' f' ≫ f') f' := ⟨pullback.snd f' f', pullback.condition.symm⟩
    let P₁ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.fst f f, rfl⟩
    let P₂ : SchemeHomOver (pullback.fst f f ≫ f) f := ⟨pullback.snd f f, pullback.condition.symm⟩
    have e₁ : schemeHomOverComp GG hGGt P₁ = mapPt e.inv hg P₁' := by
      apply Subtype.ext; show GG ≫ pullback.fst f f = _; rw [hGG1]; rfl
    have e₂ : schemeHomOverComp GG hGGt P₂ = mapPt e.inv hg P₂' := by
      apply Subtype.ext; show GG ≫ pullback.snd f f = _; rw [hGG2]; rfl
    have lhs : addMor f' L' ≫ e.inv = (L.mul _ (mapPt e.inv hg P₁') (mapPt e.inv hg P₂')).1 :=
      hmul' _ (pullback.fst f' f' ≫ f') P₁' P₂'
    have rhs : GG ≫ addMor f L = (L.mul _ (schemeHomOverComp GG hGGt P₁) (schemeHomOverComp GG hGGt P₂)).1 := by
      have := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') GG hGGt P₁ P₂)
      simp [schemeHomOverComp] at this
      exact this
    rw [lhs, rhs, e₁, e₂]
  obtain ⟨ed⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 e.inv hinv
  have pullAlong : ∀ {Z : Scheme.{u}} (q' : pullback f' f' ⟶ Z) (q : pullback f f ⟶ Z) (hq : GG ≫ q = q') (M : Z.Modules),
      (Scheme.Modules.pullback q').obj M ≅ (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback q).obj M) :=
    fun q' q hq M => (Scheme.Modules.pullbackCongr hq.symm).app M ≪≫ ((Scheme.Modules.pullbackComp GG q).app M).symm
  have eM : (Scheme.Modules.pullback (addMor f' L')).obj ((Scheme.Modules.pullback e.inv).obj 𝓛) ≅
      (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (addMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (addMor f' L') e.inv).app 𝓛 ≪≫ pullAlong _ _ hmG.symm 𝓛
  have e1 : (Scheme.Modules.pullback (pullback.fst f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e.inv).obj 𝓛)) ≅
      (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback _).mapIso ed.symm ≪≫ (Scheme.Modules.pullbackComp (pullback.fst f' f') e.inv).app _ ≪≫
      pullAlong _ _ hGG1 _
  have e2 : (Scheme.Modules.pullback (pullback.snd f' f')).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e.inv).obj 𝓛)) ≅
      (Scheme.Modules.pullback GG).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛)) :=
    (Scheme.Modules.pullback _).mapIso ed.symm ≪≫ (Scheme.Modules.pullbackComp (pullback.snd f' f') e.inv).app _ ≪≫
      pullAlong _ _ hGG2 _
  exact ⟨(eM ⊗ᵢ (e1 ⊗ᵢ e2)) ≪≫ (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso GG _ _).symm) ≪≫
    (Scheme.Modules.pullbackTensorObjIso GG _ _).symm⟩

end K2Iso
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible.K2Iso"

open K2Iso in
theorem solution
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛) := by
  intro R _ t x'
  have hg : e.inv ≫ f = f' := by rw [← he, Iso.inv_hom_id_assoc]
  have H : IsPtHom L L' e.hom he := fun T t x y => hmul t x y
  have Hi : IsPtHom L' L e.inv hg := H.inv e hg

  obtain ⟨GG, hGG1, hGG2⟩ : ∃ GG : pullback f' f' ⟶ pullback f f,
      GG ≫ pullback.fst f f = pullback.fst f' f' ≫ e.inv ∧ GG ≫ pullback.snd f f = pullback.snd f' f' ≫ e.inv :=
    ⟨pullback.lift (pullback.fst f' f' ≫ e.inv) (pullback.snd f' f' ≫ e.inv)
        (by simp only [Category.assoc, hg]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨eΛ⟩ := nonempty_mumfordBundle_iso_pullback L L' e he hg Hi 𝓛 h𝓛 GG hGG1 hGG2

  obtain ⟨x, hxv⟩ : ∃ x : SchemeHomOver t f, x.1 = x'.1 ≫ e.inv := ⟨K2Iso.mapPt e.inv hg x', rfl⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback f t ⟶ pullback f' t,
      κ ≫ pullback.fst f' t = pullback.fst f t ≫ e.hom ∧ κ ≫ pullback.snd f' t = pullback.snd f t :=
    ⟨pullback.lift (pullback.fst f t ≫ e.hom) (pullback.snd f t) (by rw [Category.assoc, he]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ', hκ'1, hκ'2⟩ : ∃ κ' : pullback f' t ⟶ pullback f t,
      κ' ≫ pullback.fst f t = pullback.fst f' t ≫ e.inv ∧ κ' ≫ pullback.snd f t = pullback.snd f' t :=
    ⟨pullback.lift (pullback.fst f' t ≫ e.inv) (pullback.snd f' t) (by rw [Category.assoc, hg]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hslice : κ ≫ sliceAt f' x' ≫ GG = sliceAt f x := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hGG1, reassoc_of% (sliceAt_fst f' x'), sliceAt_fst, reassoc_of% hκ1, Iso.hom_inv_id, Category.comp_id]
    · simp only [Category.assoc]
      rw [hGG2, reassoc_of% (sliceAt_snd f' x'), sliceAt_snd, reassoc_of% hκ2, hxv]
  have hslice' : κ' ≫ sliceAt f x = sliceAt f' x' ≫ GG := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hGG1, reassoc_of% (sliceAt_fst f' x'), sliceAt_fst, hκ'1]
    · simp only [Category.assoc]
      rw [hGG2, reassoc_of% (sliceAt_snd f' x'), sliceAt_snd, reassoc_of% hκ'2, hxv]

  have isoA : (Scheme.Modules.pullback κ).obj ((Scheme.Modules.pullback (sliceAt f' x')).obj
        (mumfordBundle f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛))) ≅
      (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) :=
    (Scheme.Modules.pullback κ).mapIso ((Scheme.Modules.pullback (sliceAt f' x')).mapIso eΛ) ≪≫
      (Scheme.Modules.pullback κ).mapIso ((Scheme.Modules.pullbackComp (sliceAt f' x') GG).app _) ≪≫
      (Scheme.Modules.pullbackComp κ (sliceAt f' x' ≫ GG)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hslice).app _
  have isoA' : (Scheme.Modules.pullback κ').obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) ≅
      (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback e.inv).obj 𝓛)) :=
    (Scheme.Modules.pullbackComp κ' (sliceAt f x)).app _ ≪≫ (Scheme.Modules.pullbackCongr hslice').app _ ≪≫
      ((Scheme.Modules.pullbackComp (sliceAt f' x') GG).app _).symm ≪≫
      ((Scheme.Modules.pullback (sliceAt f' x')).mapIso eΛ).symm
  have isoB : (Scheme.Modules.pullback κ).obj (𝟙_ (pullback f' t).Modules) ≅ 𝟙_ (pullback f t).Modules :=
    Scheme.Modules.pullbackTensorUnitObjIso κ
  have isoB' : (Scheme.Modules.pullback κ').obj (𝟙_ (pullback f t).Modules) ≅ 𝟙_ (pullback f' t).Modules :=
    Scheme.Modules.pullbackTensorUnitObjIso κ'
  have Eq := LocIsoOnBase.equivalence (pullback.snd f t)
  have Eq' := LocIsoOnBase.equivalence (pullback.snd f' t)

  have hsq : (L'.mul t x' x').1 ≫ e.inv = (L.mul t x x).1 := by
    rw [Hi _ t x' x']
    have hx : K2Iso.mapPt e.inv hg x' = x := Subtype.ext (by rw [K2Iso.mapPt_coe, hxv])
    rw [hx]
  have hone : (L'.one t).1 ≫ e.inv = (L.one t).1 := Hi.one_map t
  constructor
  · intro hx'
    have hcomm : κ ≫ pullback.snd f' t = pullback.snd f t ≫ 𝟙 _ := by rw [Category.comp_id, hκ2]
    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f t) κ (𝟙 _) hcomm hx'
    have hxL : LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ (pullback f t).Modules) :=
      Eq.trans (Eq.trans (Eq.symm (locIso_of_iso _ isoA)) h1) (locIso_of_iso _ isoB)
    have hx2 : L.mul t x x = L.one t := (h R t x).1 hxL
    apply Subtype.ext
    rw [← cancel_mono e.inv, hsq, hone]
    exact congrArg Subtype.val hx2
  · intro hx'2
    have hx2 : L.mul t x x = L.one t := by
      apply Subtype.ext
      rw [← hsq, ← hone]
      exact congrArg (fun z : SchemeHomOver t f' => z.1 ≫ e.inv) hx'2
    have hxL := (h R t x).2 hx2
    have hcomm : κ' ≫ pullback.snd f t = pullback.snd f' t ≫ 𝟙 _ := by rw [Category.comp_id, hκ'2]
    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f' t) κ' (𝟙 _) hcomm hxL
    exact Eq'.trans (Eq'.trans (Eq'.symm (locIso_of_iso _ isoA')) h1) (locIso_of_iso _ isoB')

end S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_pullback_inv_of_iso_of_isInvertible (solution)
