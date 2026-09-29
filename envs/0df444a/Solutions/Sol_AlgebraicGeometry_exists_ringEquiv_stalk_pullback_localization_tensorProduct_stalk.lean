-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b8788797-f327-5ffe-87cf-23fc376bffa8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk

set_option autoImplicit false

open TensorProduct

namespace FibreStalkBC

variable {A R S k : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing k]
  [Algebra A R] [Algebra A k] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

@[reducible] noncomputable def tensorAlgebra : Algebra (R ⊗[A] k) (S ⊗[A] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A R S) (AlgHom.id A k)).toRingHom.toAlgebra

attribute [local instance] tensorAlgebra

theorem algebraMap_tensor_tmul (r : R) (c : k) :
    algebraMap (R ⊗[A] k) (S ⊗[A] k) (r ⊗ₜ c) = algebraMap R S r ⊗ₜ c := rfl

noncomputable def cancelEquiv :
    ((R ⊗[A] k) ⊗[R] S) ≃ₐ[R ⊗[A] k] (S ⊗[A] k) := by

  let e₁ : ((R ⊗[A] k) ⊗[R] S) ≃ₐ[R] (S ⊗[R] (R ⊗[A] k)) := Algebra.TensorProduct.comm R (R ⊗[A] k) S
  let e₂ : (S ⊗[R] (R ⊗[A] k)) ≃ₐ[S] (S ⊗[A] k) := Algebra.TensorProduct.cancelBaseChange A R S S k
  refine AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂.toRingEquiv) ?_
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    change e₂ (e₁ ((r ⊗ₜ[A] c) ⊗ₜ[R] (1 : S))) = algebraMap R S r ⊗ₜ c
    simp [e₁, e₂, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem isLocalization_tensor (M : Submonoid R) [IsLocalization M S] :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) (S ⊗[A] k) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) ((R ⊗[A] k) ⊗[R] S) :=
    IsLocalization.tensor (R := R) (S := R ⊗[A] k) (A := S) M
  exact IsLocalization.isLocalization_of_algEquiv (R := R ⊗[A] k) (S := (R ⊗[A] k) ⊗[R] S) (P := S ⊗[A] k)
    (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) (cancelEquiv (A := A) (R := R) (S := S) (k := k))

end FibreStalkBC

namespace FibreStalkBC

variable {A R S k : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing k]
  [Algebra A R] [Algebra A k] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

attribute [local instance] tensorAlgebra

theorem isScalarTower_tensor : IsScalarTower R (R ⊗[A] k) (S ⊗[A] k) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := R ⊗[A] k) (A := S ⊗[A] k) fun r => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, algebraMap_tensor_tmul]

theorem core (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime S 𝔭]
    (𝔔 : Ideal (R ⊗[A] k)) [h𝔔 : 𝔔.IsPrime]
    (hQp : 𝔔.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := R) (B := k)).toRingHom = 𝔭)
    (Tq : Type*) [CommRing Tq] [Algebra (R ⊗[A] k) Tq] [IsLocalization.AtPrime Tq 𝔔]
    (φ : S →+* Tq) (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap (R ⊗[A] k) Tq (r ⊗ₜ 1)) :
    haveI := IsLocalization.AtPrime.isLocalRing S 𝔭
    ∃ (𝔮 : Ideal (S ⊗[A] k)) (_ : 𝔮.IsPrime) (e : Tq ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal S ∧
      ∀ s : S, e (φ s) = algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1) := by
  haveI := IsLocalization.AtPrime.isLocalRing S 𝔭
  haveI := isScalarTower_tensor (A := A) (R := R) (S := S) (k := k)
  set T := R ⊗[A] k
  set M : Submonoid T := Algebra.algebraMapSubmonoid T 𝔭.primeCompl with hM
  haveI hloc : IsLocalization M (S ⊗[A] k) := isLocalization_tensor 𝔭.primeCompl

  have hdisj : Disjoint (M : Set T) (𝔔 : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    rw [← hQp]
    exact hrQ

  let 𝔮 : Ideal (S ⊗[A] k) := 𝔔.map (algebraMap T (S ⊗[A] k))
  haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (S ⊗[A] k) 𝔔 h𝔔 hdisj
  have hunder : 𝔮.comap (algebraMap T (S ⊗[A] k)) = 𝔔 := IsLocalization.under_map_of_isPrime_disjoint M (S ⊗[A] k) h𝔔 hdisj

  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap T (S ⊗[A] k))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔮) 𝔮
  have hN : 𝔔.primeCompl = (Ideal.comap (algebraMap T (S ⊗[A] k)) 𝔮).primeCompl := by
    ext x
    change x ∉ 𝔔 ↔ x ∉ Ideal.comap (algebraMap T (S ⊗[A] k)) 𝔮
    rw [hunder]
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔔 := by
    change IsLocalization 𝔔.primeCompl (Localization.AtPrime 𝔮)
    rw [hN]
    exact this
  let e : Tq ≃ₐ[T] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔔.primeCompl Tq (Localization.AtPrime 𝔮)
  refine ⟨𝔮, h𝔮, e.toRingEquiv, ?_, ?_⟩
  ·
    have hle : IsLocalRing.maximalIdeal S ≤ 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 S, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change algebraMap R S r ⊗ₜ[A] (1 : k) ∈ 𝔮
      rw [← algebraMap_tensor_tmul]
      apply Ideal.mem_map_of_mem
      rw [← hQp] at hr
      exact hr
    refine ((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le ?_ hle).symm
    intro htop
    apply h𝔮.ne_top
    rw [Ideal.eq_top_iff_one] at htop ⊢
    simp at htop
    exact htop
  ·
    intro s
    suffices h : (e.toRingEquiv.toRingHom.comp φ) =
        (algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮)).comp
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom by
      exact congrArg (fun f : S →+* Localization.AtPrime 𝔮 => f s) h
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext r
    change e (φ (algebraMap R S r)) = algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮) (algebraMap R S r ⊗ₜ[A] 1)
    rw [hφ, ← algebraMap_tensor_tmul, ← IsScalarTower.algebraMap_apply]
    exact e.commutes (r ⊗ₜ 1)

end FibreStalkBC

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 6400000 in
theorem solution
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (k : Type u) [CommRing k] [Algebra A k]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))) :
    letI z := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base x
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := X.presheaf.stalk z) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      ∀ s : X.presheaf.stalk z,
        e (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1) := by
  classical

  let 𝒰 := X.affineOpenCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰.openCover f (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  obtain ⟨j, y, hyx⟩ := 𝒱.exists_eq x
  set Rj : CommRingCat := 𝒰.X j with hRj
  set fj : Spec Rj ⟶ X := 𝒰.f j with hfj

  let φ : CommRingCat.of A ⟶ Rj := (Spec.fullyFaithful.preimage (fj ≫ f)).unop
  have hφ : Spec.map φ = fj ≫ f := Spec.fullyFaithful.map_preimage (fj ≫ f)
  letI : Algebra A Rj := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap A Rj) = φ := rfl

  let ec : pullback (Spec.map (CommRingCat.ofHom (algebraMap A Rj))) (Spec.map (CommRingCat.ofHom (algebraMap A k))) ≅ 𝒱.X j :=
    pullback.congrHom (by rw [hφ', hφ]; rfl) rfl
  let eT : Spec (CommRingCat.of (Rj ⊗[A] k)) ≅ 𝒱.X j := (pullbackSpecIso A Rj k).symm ≪≫ ec
  obtain ⟨w, hw⟩ := (Scheme.homeoOfIso eT).surjective y
  set ι : Spec (CommRingCat.of (Rj ⊗[A] k)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))) := eT.hom ≫ 𝒱.f j with hι
  have hxι : ι.base w = x := by
    rw [← hyx, ← hw, Scheme.coe_homeoOfIso, hι]; rfl
  have hιfst : ι ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := (Rj : Type u)) (B := k))) ≫ fj := by
    simp only [hι, eT, ec, 𝒱, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom,
      Scheme.Pullback.openCoverOfLeft_f, Category.assoc]
    erw [pullback.lift_fst]
    erw [pullback.lift_fst_assoc]
    simp only [Category.comp_id, Category.assoc]
    erw [pullbackSpecIso_inv_fst_assoc]
    rfl
  set T : Type u := (Rj : Type u) ⊗[A] k with hT
  set incl : CommRingCat.of (Rj : Type u) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := (Rj : Type u)) (B := k)) with hincl
  set w₁ : PrimeSpectrum Rj := PrimeSpectrum.comap incl.hom w with hw₁
  have hw₁' : (Spec.map incl).base w = w₁ := rfl
  have hzpt : (ι ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k))))).base w = (Spec.map incl ≫ fj).base w := by rw [hιfst]
  have hz₁ : (Spec.map incl ≫ fj).base w = fj.base w₁ := rfl

  have hfjIO : IsOpenImmersion fj := 𝒰.map_prop j
  haveI : IsIso (fj.stalkMap w₁) := (IsOpenImmersion.iff_isIso_stalkMap.mp hfjIO).2 w₁
  haveI hιIO : IsOpenImmersion ι := by rw [hι]; infer_instance
  haveI : IsIso (ι.stalkMap w) := (IsOpenImmersion.iff_isIso_stalkMap.mp hιIO).2 w
  let eZ : X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) ≅ X.presheaf.stalk (fj.base w₁) :=
    X.presheaf.stalkCongr (.of_eq hzpt)
  let eJ : X.presheaf.stalk (fj.base w₁) ≅ (Spec Rj).presheaf.stalk w₁ := asIso (fj.stalkMap w₁)
  let eS : X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) ≅ CommRingCat.of (Localization.AtPrime w₁.asIdeal) :=
    eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj w₁
  let rS : (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) : Type u) ≃+* Localization.AtPrime w₁.asIdeal :=
    eS.commRingCatIsoToRingEquiv

  letI algRjS : Algebra Rj (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w))) :=
    (rS.symm.toRingHom.comp (algebraMap Rj (Localization.AtPrime w₁.asIdeal))).toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) : Type u) w₁.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv (R := Rj) (S := Localization.AtPrime w₁.asIdeal) w₁.asIdeal.primeCompl
      (AlgEquiv.ofRingEquiv (f := rS.symm) (fun r => rfl))

  letI instA : Algebra A (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w))) :=
    ((X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra

  have hrS : ∀ a : A, rS (X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      algebraMap Rj (Localization.AtPrime w₁.asIdeal) (φ a) := by
    intro a

    change (Spec.stalkIso Rj w₁).hom (fj.stalkMap w₁ (eZ.hom
      (X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))))) = _

    have s1 : eZ.hom (X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) trivial
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
        X.presheaf.germ ⊤ (fj.base w₁) trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
      simp only [eZ, TopCat.Presheaf.stalkCongr_hom]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf (U := ⊤) trivial (Inseparable.of_eq hzpt).ge _
    rw [s1]

    erw [Scheme.Hom.germ_stalkMap_apply fj ⊤ w₁ trivial]

    have s345 : fj.app ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
        (Scheme.ΓSpecIso Rj).inv (φ a) := by
      have h1 : fj.app ⊤ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
          (fj ≫ f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
        rw [Scheme.Hom.comp_appTop]; rfl
      rw [h1, ← hφ]
      have h2 := Scheme.ΓSpecIso_inv_naturality φ
      have h3 := congrArg (fun g : CommRingCat.of A ⟶ Γ(Spec Rj, ⊤) => g.hom a) h2
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      exact h3.symm
    erw [s345]

    have s6 := congrArg (fun g : Γ(Spec Rj, ⊤) ⟶ CommRingCat.of (Localization.AtPrime w₁.asIdeal) =>
      g.hom ((Scheme.ΓSpecIso Rj).inv (φ a))) (Spec.germ_stalkMapIso_hom w₁)
    simp only [CommRingCat.comp_apply] at s6
    erw [s6]
    simp
  haveI : IsScalarTower A Rj (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w))) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      apply rS.injective
      change rS (X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
        rS (rS.symm (algebraMap Rj (Localization.AtPrime w₁.asIdeal) (φ.hom a)))
      rw [hrS, RingEquiv.apply_symm_apply]

  let φS : (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) : Type u) →+* Localization.AtPrime w.asIdeal :=
    (Spec.stalkIso (CommRingCat.of T) w).hom.hom.comp ((ι.stalkMap w).hom.comp ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap (ι.base w)).hom)
  have hφS : ∀ r : Rj, φS (algebraMap Rj _ r) = algebraMap T (Localization.AtPrime w.asIdeal) (r ⊗ₜ 1) := by
    intro r
    change (Spec.stalkIso (CommRingCat.of T) w).hom (ι.stalkMap w ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap (ι.base w)
      (rS.symm (algebraMap Rj (Localization.AtPrime w₁.asIdeal) r)))) = _

    have t1 : ∀ v, ι.stalkMap w ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap (ι.base w) v) = (ι ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k))))).stalkMap w v :=
      fun v => (congrArg (fun g : X.presheaf.stalk _ ⟶ _ => g.hom v) (Scheme.Hom.stalkMap_comp ι (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))) w)).symm
    rw [t1]

    rw [Scheme.Hom.stalkMap_congr_hom _ _ hιfst w]

    rw [Scheme.Hom.stalkMap_comp]
    change (Spec.stalkIso (CommRingCat.of T) w).hom ((Spec.map incl).stalkMap w (fj.stalkMap w₁ (eZ.hom
      (rS.symm (algebraMap Rj (Localization.AtPrime w₁.asIdeal) r))))) = _

    have t4 : ∀ q, rS.symm q = eZ.inv (eJ.inv ((Spec.stalkIso Rj w₁).inv q)) := fun q => rfl
    rw [t4, Iso.inv_hom_id_apply]
    have t5 : ∀ u, fj.stalkMap w₁ (eJ.inv u) = u := fun u => Iso.inv_hom_id_apply eJ u
    rw [t5]

    have t6 := congrArg (fun g : (Spec Rj).presheaf.stalk w₁ ⟶ (Spec (CommRingCat.of T)).presheaf.stalk w =>
      (Spec.stalkIso (CommRingCat.of T) w).hom (g ((Spec.stalkIso Rj w₁).inv (algebraMap Rj (Localization.AtPrime w₁.asIdeal) r))))
      (Scheme.localRingHom_comp_stalkIso incl w).symm
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] at t6
    erw [t6]
    change (Spec.stalkIso (CommRingCat.of T) w).hom ((Spec.stalkIso (CommRingCat.of T) w).inv
      (Localization.localRingHom w₁.asIdeal w.asIdeal incl.hom rfl ((Spec.stalkIso Rj w₁).hom ((Spec.stalkIso Rj w₁).inv
        (algebraMap Rj (Localization.AtPrime w₁.asIdeal) r))))) = _
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, Localization.localRingHom_to_map]
    rfl

  have hQp : (w.asIdeal).comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := (Rj : Type u)) (B := k)).toRingHom =
      w₁.asIdeal := rfl
  obtain ⟨𝔮, h𝔮, e, hcomap, hcompat⟩ :=
    FibreStalkBC.core (A := A) (R := (Rj : Type u)) (S := (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base (ι.base w)) : Type u)) (k := k)
      w₁.asIdeal w.asIdeal hQp (Localization.AtPrime w.asIdeal) φS hφS
  subst hxι
  exact ⟨𝔮, h𝔮, ((asIso (ι.stalkMap w)) ≪≫ Spec.stalkIso (CommRingCat.of T) w).commRingCatIsoToRingEquiv.trans e, hcomap,
    fun s => hcompat s⟩

end S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk (solution)
