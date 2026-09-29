-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bfcec3ed-6a51-5524-9459-daf397ccd6cf

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_inv_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace Ws23Sqrt

variable {R : Type u} [CommRing R]

def IsPtHom {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    (L.mul t x y).1 ≫ φ = (L'.mul t (mapPt φ hφ x) (mapPt φ hφ y)).1

theorem IsPtHom.inv {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {L : RelativeGroupLaw R f} {L' : RelativeGroupLaw R f'} (e : A ≅ A') {he : e.hom ≫ f' = f}
    (h : IsPtHom L L' e.hom he) (hei : e.inv ≫ f = f') : IsPtHom L' L e.inv hei := by
  intro T t x y
  have h1 := h T t (mapPt e.inv hei x) (mapPt e.inv hei y)
  have ex : mapPt e.hom he (mapPt e.inv hei x) = x := Subtype.ext (by simp [mapPt_coe])
  have ey : mapPt e.hom he (mapPt e.inv hei y) = y := Subtype.ext (by simp [mapPt_coe])
  rw [ex, ey] at h1
  rw [← cancel_mono e.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h1.symm

theorem mul_val_congr {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P P' Q Q' : SchemeHomOver t f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (L.mul t P Q).1 = (L.mul t P' Q').1 := by
  cases Subtype.ext hP; cases Subtype.ext hQ; rfl

theorem schemeHomOverComp_inv {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  letI : Group (SchemeHomOver t' f) := L.pointGroup t'
  let Φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (fun x => schemeHomOverComp ψ hψ x) (fun x y => L.mul_natural t t' ψ hψ x y)
  exact map_inv Φ x

theorem comp_negMor {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    x.1 ≫ negMor f L = (L.inv t x).1 := by
  have h := schemeHomOverComp_inv L f t x.1 x.2 (idPt f)
  have h2 : schemeHomOverComp x.1 x.2 (idPt f) = x := by apply Subtype.ext; simp [schemeHomOverComp, idPt]
  rw [h2] at h
  have := congrArg Subtype.val h
  simpa [schemeHomOverComp, negMor] using this

theorem locIso_of_iso {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) {M M' : X.Modules} (i : M ≅ M') :
    LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso i⟩⟩

section Conj

theorem schemeHomOverComp_mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ρ : T' ⟶ T) (hρ : ρ ≫ t = t') (P : SchemeHomOver t f) :
    schemeHomOverComp ρ hρ (mapPt φ hφ P) = mapPt φ hφ (schemeHomOverComp ρ hρ P) :=
  Subtype.ext (by simp [mapPt_coe, schemeHomOverComp])

variable {B B' : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {g' : B' ⟶ Spec (CommRingCat.of R)}
  (κ : B ≅ B') (hκ : κ.hom ≫ g' = g)

include κ hκ

theorem inv_over : κ.inv ≫ g = g' := by rw [← hκ, Iso.inv_hom_id_assoc]

@[scoped simp] theorem mapPt_hom_inv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t g') :
    mapPt κ.hom hκ (mapPt κ.inv (inv_over κ hκ) P) = P :=
  Subtype.ext (by simp [mapPt_coe])

@[scoped simp] theorem mapPt_inv_hom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t g) :
    mapPt κ.inv (inv_over κ hκ) (mapPt κ.hom hκ P) = P :=
  Subtype.ext (by simp [mapPt_coe])

def conjLaw (L' : RelativeGroupLaw R g') : RelativeGroupLaw R g where
  mul t P Q := mapPt κ.inv (inv_over κ hκ) (L'.mul t (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q))
  one t := mapPt κ.inv (inv_over κ hκ) (L'.one t)
  inv t P := mapPt κ.inv (inv_over κ hκ) (L'.inv t (mapPt κ.hom hκ P))
  mul_assoc t x y z := by simp only [mapPt_hom_inv]; rw [L'.mul_assoc]
  one_mul t x := by simp only [mapPt_hom_inv]; rw [L'.one_mul, mapPt_inv_hom]
  mul_one t x := by simp only [mapPt_hom_inv]; rw [L'.mul_one, mapPt_inv_hom]
  inv_mul_cancel t x := by simp only [mapPt_hom_inv]; rw [L'.inv_mul_cancel]
  mul_natural t t' ρ hρ x y := by
    rw [schemeHomOverComp_mapPt, L'.mul_natural t t' ρ hρ, schemeHomOverComp_mapPt, schemeHomOverComp_mapPt]

theorem conjLaw_mul_val (L' : RelativeGroupLaw R g') {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t g) :
    ((conjLaw κ hκ L').mul t P Q).1 = (L'.mul t (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q)).1 ≫ κ.inv := rfl

theorem conjLaw_inv_val (L' : RelativeGroupLaw R g') {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t g) :
    ((conjLaw κ hκ L').inv t P).1 = (L'.inv t (mapPt κ.hom hκ P)).1 ≫ κ.inv := rfl

theorem conjLaw_hom (L' : RelativeGroupLaw R g') {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g) :
    ((conjLaw κ hκ L').mul t x y).1 ≫ κ.hom =
      (L'.mul t ⟨x.1 ≫ κ.hom, by rw [Category.assoc, hκ]; exact x.2⟩ ⟨y.1 ≫ κ.hom, by rw [Category.assoc, hκ]; exact y.2⟩).1 := by
  rw [conjLaw_mul_val, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem conjLaw_negMor (L' : RelativeGroupLaw R g') :
    κ.inv ≫ negMor g (conjLaw κ hκ L') = negMor g' L' ≫ κ.inv := by
  rw [comp_negMor (conjLaw κ hκ L') g' ⟨κ.inv, inv_over κ hκ⟩, conjLaw_inv_val]
  have hid : mapPt κ.hom hκ (⟨κ.inv, inv_over κ hκ⟩ : SchemeHomOver g' g) = idPt g' :=
    Subtype.ext (by simp [mapPt_coe, idPt])
  rw [hid]
  rfl

end Conj

theorem mul_val_congr' {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h; cases Subtype.ext hP; cases Subtype.ext hQ; rfl

theorem compose {S S' S₂ : Type u} [CommRing S] [CommRing S'] [CommRing S₂]
    (ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (ι₂ : Spec (CommRingCat.of S₂) ⟶ Spec (CommRingCat.of S'))
    (ι₁ : Spec (CommRingCat.of S₂) ⟶ Spec (CommRingCat.of S)) (hι : ι₁ = ι₂ ≫ ι)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (L' : RelativeGroupLaw S' (pullback.snd f ι))
    (hL' : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f ι)),
        (L'.mul t' P Q).1 ≫ pullback.fst f ι =
          (L.mul (t' ≫ ι)
            ⟨P.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules)
    (H : ∀ (L₂ : RelativeGroupLaw S₂ (pullback.snd (pullback.snd f ι) ι₂)),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' (pullback.snd (pullback.snd f ι) ι₂)),
            (L₂.mul t' P Q).1 ≫ pullback.fst (pullback.snd f ι) ι₂ =
              (L'.mul (t' ≫ ι₂)
                ⟨P.1 ≫ pullback.fst (pullback.snd f ι) ι₂, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst (pullback.snd f ι) ι₂, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback (pullback.snd f ι) ι₂).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd (pullback.snd f ι) ι₂) L₂ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd (pullback.snd f ι) ι₂)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd f ι) ι₂)).obj ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (pullback.snd f ι) ι₂) L₂)).obj 𝓛₀))
    (L₁ : RelativeGroupLaw S₂ (pullback.snd f ι₁))
    (hL₁ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' (pullback.snd f ι₁)),
        (L₁.mul t' P Q).1 ≫ pullback.fst f ι₁ =
          (L.mul (t' ≫ ι₁)
            ⟨P.1 ≫ pullback.fst f ι₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f ι₁, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ 𝓛₀ : (pullback f ι₁).Modules,
      Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f ι₁) L₁ 𝓛₀ ∧
      LocIsoOnBase (pullback.snd f ι₁)
        ((Scheme.Modules.pullback (pullback.fst f ι₁)).obj 𝓛)
        (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f ι₁) L₁)).obj 𝓛₀) := by
  subst hι

  have w₁ : pullback.fst f (ι₂ ≫ ι) ≫ f = (pullback.snd f (ι₂ ≫ ι) ≫ ι₂) ≫ ι := by
    rw [pullback.condition, Category.assoc]

  let r : pullback f (ι₂ ≫ ι) ⟶ pullback f ι := pullback.lift (pullback.fst f (ι₂ ≫ ι)) (pullback.snd f (ι₂ ≫ ι) ≫ ι₂) w₁
  have hr1 : r ≫ pullback.fst f ι = pullback.fst f (ι₂ ≫ ι) := pullback.lift_fst _ _ _
  have hr2 : r ≫ pullback.snd f ι = pullback.snd f (ι₂ ≫ ι) ≫ ι₂ := pullback.lift_snd _ _ _
  have w₂ : (pullback.fst (pullback.snd f ι) ι₂ ≫ pullback.fst f ι) ≫ f =
      pullback.snd (pullback.snd f ι) ι₂ ≫ ι₂ ≫ ι := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  let κ : pullback (pullback.snd f ι) ι₂ ≅ pullback f (ι₂ ≫ ι) :=
    { hom := pullback.lift (pullback.fst (pullback.snd f ι) ι₂ ≫ pullback.fst f ι) (pullback.snd (pullback.snd f ι) ι₂) w₂
      inv := pullback.lift r (pullback.snd f (ι₂ ≫ ι)) hr2
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, hr1, pullback.lift_fst]
          · rw [Category.assoc, hr2, ← Category.assoc, pullback.lift_snd, pullback.condition]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hr1, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hκ : κ.hom ≫ pullback.snd f (ι₂ ≫ ι) = pullback.snd (pullback.snd f ι) ι₂ := pullback.lift_snd _ _ _
  have hκ1 : κ.hom ≫ pullback.fst f (ι₂ ≫ ι) = pullback.fst (pullback.snd f ι) ι₂ ≫ pullback.fst f ι := pullback.lift_fst _ _ _
  have hκi : κ.inv ≫ pullback.snd (pullback.snd f ι) ι₂ = pullback.snd f (ι₂ ≫ ι) := pullback.lift_snd _ _ _
  have hκi1 : κ.inv ≫ pullback.fst (pullback.snd f ι) ι₂ = r := pullback.lift_fst _ _ _

  let L₂ : RelativeGroupLaw S₂ (pullback.snd (pullback.snd f ι) ι₂) := conjLaw κ hκ L₁
  have hL₂ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' (pullback.snd (pullback.snd f ι) ι₂)),
      (L₂.mul t' P Q).1 ≫ pullback.fst (pullback.snd f ι) ι₂ =
        (L'.mul (t' ≫ ι₂)
          ⟨P.1 ≫ pullback.fst (pullback.snd f ι) ι₂, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst (pullback.snd f ι) ι₂, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    show ((L₁.mul t' (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q)).1 ≫ κ.inv) ≫ pullback.fst (pullback.snd f ι) ι₂ = _
    rw [Category.assoc, hκi1]
    apply pullback.hom_ext
    · rw [Category.assoc, hr1, hL₁, hL']
      apply mul_val_congr' L (Category.assoc _ _ _).symm
      · simp only [mapPt_coe, Category.assoc]
        rw [hκ1]
      · simp only [mapPt_coe, Category.assoc]
        rw [hκ1]
    · rw [Category.assoc, hr2, ← Category.assoc, (L₁.mul t' (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q)).2,
        (L'.mul (t' ≫ ι₂) _ _).2]
  obtain ⟨𝓛₀, h0inv, h0K, h0loc⟩ := H L₂ hL₂
  refine ⟨(Scheme.Modules.pullback κ.inv).obj 𝓛₀, Scheme.Modules.IsInvertible.pullback κ.inv h0inv, ?_, ?_⟩
  ·
    exact AlgebraicGeometry.Polarisation.kernelTrivial_pullback_inv_of_iso L₂ L₁ κ hκ
      (fun t x y => conjLaw_hom κ hκ L₁ t x y) 𝓛₀ h0inv h0K
  ·
    have Eq := LocIsoOnBase.equivalence (pullback.snd f (ι₂ ≫ ι))
    have hcomm : κ.inv ≫ pullback.snd (pullback.snd f ι) ι₂ = pullback.snd f (ι₂ ≫ ι) ≫ 𝟙 _ := by rw [Category.comp_id, hκi]
    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (ι₂ ≫ ι)) κ.inv (𝟙 _) hcomm h0loc
    have iso1 : (Scheme.Modules.pullback κ.inv).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f ι) ι₂)).obj ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛)) ≅
        (Scheme.Modules.pullback (pullback.fst f (ι₂ ≫ ι))).obj 𝓛 :=
      (Scheme.Modules.pullbackComp κ.inv (pullback.fst (pullback.snd f ι) ι₂)).app _ ≪≫
        (Scheme.Modules.pullbackCongr hκi1).app _ ≪≫
        (Scheme.Modules.pullbackComp r (pullback.fst f ι)).app 𝓛 ≪≫
        (Scheme.Modules.pullbackCongr hr1).app 𝓛
    have hneg : κ.inv ≫ negMor (pullback.snd (pullback.snd f ι) ι₂) L₂ = negMor (pullback.snd f (ι₂ ≫ ι)) L₁ ≫ κ.inv :=
      conjLaw_negMor κ hκ L₁
    have iso2 : (Scheme.Modules.pullback κ.inv).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (pullback.snd f ι) ι₂) L₂)).obj 𝓛₀) ≅
        (Scheme.Modules.pullback κ.inv).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f (ι₂ ≫ ι)) L₁)).obj ((Scheme.Modules.pullback κ.inv).obj 𝓛₀) :=
      Scheme.Modules.pullbackTensorObjIso κ.inv _ _ ≪≫
        (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullbackComp κ.inv (negMor (pullback.snd (pullback.snd f ι) ι₂) L₂)).app 𝓛₀ ≪≫
          (Scheme.Modules.pullbackCongr hneg).app 𝓛₀ ≪≫
          ((Scheme.Modules.pullbackComp (negMor (pullback.snd f (ι₂ ≫ ι)) L₁) κ.inv).app 𝓛₀).symm))
    exact Eq.trans (Eq.trans (Eq.symm (locIso_of_iso _ iso1)) h1) (locIso_of_iso _ iso2)

end Ws23Sqrt
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat.Ws23Sqrt"

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (S' : Type u) [CommRing S'] [Algebra S S'] (hff : Module.FaithfullyFlat S S')
    (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : (∃ (S₂ : Type u) (_ : CommRing S₂) (_ : Algebra S' S₂),
      Module.FaithfullyFlat S' S₂ ∧
      ∀ (L₂ : RelativeGroupLaw S₂ (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))),
            (L₂.mul t' P Q).1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))) =
              (L'.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
                ⟨P.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂))))).obj ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))) L₂)).obj 𝓛₀))) :
    (∃ (S₁ : Type u) (_ : CommRing S₁) (_ : Algebra S S₁),
      Module.FaithfullyFlat S S₁ ∧
      ∀ (L₁ : RelativeGroupLaw S₁ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S₁)) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S₁))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S₁)))) L₁)).obj 𝓛₀)) := by
  obtain ⟨S₂, instC, instA, hff₂, H⟩ := h
  letI : CommRing S₂ := instC
  letI : Algebra S' S₂ := instA
  letI algS : Algebra S S₂ := ((algebraMap S' S₂).comp (algebraMap S S')).toAlgebra
  haveI : IsScalarTower S S' S₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.FaithfullyFlat S S' := hff
  haveI : Module.FaithfullyFlat S' S₂ := hff₂
  have hffc : Module.FaithfullyFlat S S₂ := Module.FaithfullyFlat.trans S S' S₂
  have hι : Spec.map (CommRingCat.ofHom (algebraMap S S₂)) =
      Spec.map (CommRingCat.ofHom (algebraMap S' S₂)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact ⟨S₂, instC, algS, hffc, fun L₁ hL₁ =>
    Ws23Sqrt.compose (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)))
      (Spec.map (CommRingCat.ofHom (algebraMap S S₂))) hι f L L' hL' 𝓛 H L₁ hL₁⟩

end S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_principalSqrt_of_exists_pullback_of_faithfullyFlat (solution)
