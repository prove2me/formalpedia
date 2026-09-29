-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d5a7bf85-d366-5d47-8525-1dfb4190394f

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_inv_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace CaRoot

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

theorem core {S S' : Type u} [CommRing S] [CommRing S']
    (σ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    (e : A ≅ A') (he : e.hom ≫ f' = f) (hmul : IsPtHom L L' e.hom he) (𝓛 : A.Modules)
    (H : ∀ (L₁ : RelativeGroupLaw S' (pullback.snd f σ)),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f σ)),
            (L₁.mul t' P Q).1 ≫ pullback.fst f σ =
              (L.mul (t' ≫ σ)
                ⟨P.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f σ).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f σ) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f σ)
            ((Scheme.Modules.pullback (pullback.fst f σ)).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f σ) L₁)).obj 𝓛₀))
    (L₁' : RelativeGroupLaw S' (pullback.snd f' σ))
    (hL₁' : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f' σ)),
            (L₁'.mul t' P Q).1 ≫ pullback.fst f' σ =
              (L'.mul (t' ≫ σ)
                ⟨P.1 ≫ pullback.fst f' σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f' σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ 𝓛₀ : (pullback f' σ).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f' σ) L₁' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f' σ)
            ((Scheme.Modules.pullback (pullback.fst f' σ)).obj ((Scheme.Modules.pullback e.inv).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f' σ) L₁')).obj 𝓛₀) := by
  have hei : e.inv ≫ f = f' := by rw [← he, Iso.inv_hom_id_assoc]

  let κ : pullback f σ ≅ pullback f' σ :=
    { hom := pullback.lift (pullback.fst f σ ≫ e.hom) (pullback.snd f σ) (by rw [Category.assoc, he, pullback.condition])
      inv := pullback.lift (pullback.fst f' σ ≫ e.inv) (pullback.snd f' σ) (by rw [Category.assoc, hei, pullback.condition])
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, Iso.hom_inv_id,
            Category.comp_id, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, Iso.inv_hom_id,
            Category.comp_id, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp] }
  have hκ : κ.hom ≫ pullback.snd f' σ = pullback.snd f σ := pullback.lift_snd _ _ _
  have hκi : κ.inv ≫ pullback.snd f σ = pullback.snd f' σ := pullback.lift_snd _ _ _
  have hκ1 : κ.hom ≫ pullback.fst f' σ = pullback.fst f σ ≫ e.hom := pullback.lift_fst _ _ _
  have hκi1 : κ.inv ≫ pullback.fst f σ = pullback.fst f' σ ≫ e.inv := pullback.lift_fst _ _ _

  let L₁ : RelativeGroupLaw S' (pullback.snd f σ) := conjLaw κ hκ L₁'
  have hmuli : IsPtHom L' L e.inv hei := IsPtHom.inv e hmul hei
  have hL₁ : ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f σ)),
      (L₁.mul t' P Q).1 ≫ pullback.fst f σ =
        (L.mul (t' ≫ σ)
          ⟨P.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f σ, by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    show ((L₁'.mul t' (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q)).1 ≫ κ.inv) ≫ pullback.fst f σ = _
    rw [Category.assoc, hκi1, ← Category.assoc, hL₁' T t' (mapPt κ.hom hκ P) (mapPt κ.hom hκ Q), hmuli _ (t' ≫ σ)]
    apply mul_val_congr
    · simp only [mapPt_coe, Category.assoc]
      rw [reassoc_of% hκ1, Iso.hom_inv_id, Category.comp_id]
    · simp only [mapPt_coe, Category.assoc]
      rw [reassoc_of% hκ1, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨𝓛₀, h0inv, h0K, h0loc⟩ := H L₁ hL₁
  refine ⟨(Scheme.Modules.pullback κ.inv).obj 𝓛₀, Scheme.Modules.IsInvertible.pullback κ.inv h0inv, ?_, ?_⟩
  ·
    exact AlgebraicGeometry.Polarisation.kernelTrivial_pullback_inv_of_iso L₁ L₁' κ hκ
      (fun t x y => conjLaw_hom κ hκ L₁' t x y) 𝓛₀ h0inv h0K
  ·
    have Eq := LocIsoOnBase.equivalence (pullback.snd f' σ)
    have hcomm : κ.inv ≫ pullback.snd f σ = pullback.snd f' σ ≫ 𝟙 _ := by rw [Category.comp_id, hκi]
    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f' σ) κ.inv (𝟙 _) hcomm h0loc
    have iso1 : (Scheme.Modules.pullback κ.inv).obj ((Scheme.Modules.pullback (pullback.fst f σ)).obj 𝓛) ≅
        (Scheme.Modules.pullback (pullback.fst f' σ)).obj ((Scheme.Modules.pullback e.inv).obj 𝓛) :=
      (Scheme.Modules.pullbackComp κ.inv (pullback.fst f σ)).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hκi1).app 𝓛 ≪≫
        ((Scheme.Modules.pullbackComp (pullback.fst f' σ) e.inv).app 𝓛).symm
    have hneg : κ.inv ≫ negMor (pullback.snd f σ) L₁ = negMor (pullback.snd f' σ) L₁' ≫ κ.inv := conjLaw_negMor κ hκ L₁'
    have iso2 : (Scheme.Modules.pullback κ.inv).obj (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f σ) L₁)).obj 𝓛₀) ≅
        (Scheme.Modules.pullback κ.inv).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f' σ) L₁')).obj ((Scheme.Modules.pullback κ.inv).obj 𝓛₀) :=
      Scheme.Modules.pullbackTensorObjIso κ.inv _ _ ≪≫
        (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullbackComp κ.inv (negMor (pullback.snd f σ) L₁)).app 𝓛₀ ≪≫
          (Scheme.Modules.pullbackCongr hneg).app 𝓛₀ ≪≫
          ((Scheme.Modules.pullbackComp (negMor (pullback.snd f' σ) L₁') κ.inv).app 𝓛₀).symm))
    exact Eq.trans (Eq.trans (Eq.symm (locIso_of_iso _ iso1)) h1) (locIso_of_iso _ iso2)

end CaRoot
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso.CaRoot"

theorem solution
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f')
    (e : A ≅ A') (he : e.hom ≫ f' = f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
      (L.mul t x y).1 ≫ e.hom =
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L₁ : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj (𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₁)).obj 𝓛₀))) :
    (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L₁ : RelativeGroupLaw S' (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L₁.mul t' P Q).1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L'.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f' (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₁ 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj ((Scheme.Modules.pullback e.inv).obj 𝓛))
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L₁)).obj 𝓛₀)) := by
  obtain ⟨S', i1, i2, hff, H⟩ := h
  exact ⟨S', i1, i2, hff, fun L₁' hL₁' =>
    CaRoot.core (Spec.map (CommRingCat.ofHom (algebraMap S S'))) L L' e he (fun T t x y => hmul t x y) 𝓛 H L₁' hL₁'⟩

end S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_faithfullyFlat_kernelTrivial_locIsoOnBase_pullback_inv_of_iso (solution)
