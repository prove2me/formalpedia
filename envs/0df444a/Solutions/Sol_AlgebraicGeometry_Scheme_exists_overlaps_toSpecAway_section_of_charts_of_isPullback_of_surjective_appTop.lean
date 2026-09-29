-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f9b0cc12-f932-596b-9a06-25945c2c8c4f

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_toSpecAway_of_charts_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isPullback_fst_fst_toSpecAway_of_charts_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace R0Aux

theorem eq_of_comp_toSpec_eq {S : Type u} [CommRing S] (M : Submonoid S) (L : Type u) [CommRing L] [Algebra S L]
    [IsLocalization M L] {C : Type u} [CommRing C]
    (u v : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of L))
    (h : u ≫ Spec.map (CommRingCat.ofHom (algebraMap S L)) = v ≫ Spec.map (CommRingCat.ofHom (algebraMap S L))) :
    u = v := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective u
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext1
  apply IsLocalization.ringHom_ext M
  ext x
  exact congrArg (fun t : CommRingCat.of S ⟶ CommRingCat.of C => t.hom x) h

noncomputable def liftAway {S : Type u} [CommRing S] (y : S) (By : Type u) [CommRing By] [Algebra S By]
    [IsLocalization.Away y By] (P : Type u) [CommRing P] [Algebra S P] (hy : IsUnit (algebraMap S P y)) :
    By →ₐ[S] P :=
  { toRingHom := IsLocalization.Away.lift y hy
    commutes' := fun s => IsLocalization.Away.lift_eq y hy s }

end R0Aux

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j) :
    ∃ (ρ₁ : ∀ i j : Fin k, B i →ₐ[S] Localization.Away (r i * r j))
      (ρ₂ : ∀ i j : Fin k, B j →ₐ[S] Localization.Away (r i * r j))
      (fP : ∀ i j : Fin k,
        Limits.pullback (ι i) (ι j) ⟶ Spec (CommRingCat.of (Localization.Away (r i * r j))))
      (eP : ∀ i j : Fin k,
        Spec (CommRingCat.of (Localization.Away (r i * r j))) ⟶ Limits.pullback (ι i) (ι j)),

      (∀ i j, eP i j ≫ fP i j = 𝟙 _) ∧
      (∀ i j, fP i j ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) =
        Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ∧
      (∀ i j, eP i j ≫ Limits.pullback.fst (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ e i) ∧
      (∀ i j, eP i j ≫ Limits.pullback.snd (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ e j) ∧
      (∀ i j, Function.Surjective ((fP i j).appTop).hom) ∧
      (∀ (i j : Fin k) (r' : Localization.Away (r i * r j)), Function.Surjective
        ((pullback.snd (fP i j) (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away (r i * r j)) (Localization.Away r'))))).appTop).hom) ∧

      (∀ (i j l : Fin k)
        (π₁₃ : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
          Limits.pullback (ι i) (ι l))
        (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) =
          (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.fst (ι i) (ι j))
        (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) =
          (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫
            Limits.pullback.snd (ι j) (ι l)),
        ∃ (fT : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶
              Spec (CommRingCat.of (Localization.Away (r i * r j * r l))))
          (eT : Spec (CommRingCat.of (Localization.Away (r i * r j * r l))) ⟶
              Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))
          (σ₁₂ : Localization.Away (r i * r j) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₂₃ : Localization.Away (r j * r l) →ₐ[S] Localization.Away (r i * r j * r l))
          (σ₁₃ : Localization.Away (r i * r l) →ₐ[S] Localization.Away (r i * r j * r l)),
          eT ≫ fT = 𝟙 _ ∧ Function.Surjective (fT.appTop).hom ∧
          eT ≫ Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₁₂.toRingHom) ≫ eP i j ∧
          eT ≫ Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) =
            Spec.map (CommRingCat.ofHom σ₂₃.toRingHom) ≫ eP j l ∧
          eT ≫ π₁₃ = Spec.map (CommRingCat.ofHom σ₁₃.toRingHom) ≫ eP i l) := by
  classical

  have hP := fun i j =>
    AlgebraicGeometry.Scheme.exists_isPullback_fst_toSpecAway_of_charts_of_isPullback r B f f' ι hsq i j
  choose ρ₁ fP hloc hsqP hoverP using hP

  have hE : ∀ i j : Fin k, ∃ eP : Spec (CommRingCat.of (Localization.Away (r i * r j))) ⟶ Limits.pullback (ι i) (ι j),
      eP ≫ fP i j = 𝟙 _ ∧
      eP ≫ Limits.pullback.fst (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ e i ∧
      Function.Surjective ((fP i j).appTop).hom ∧
      ∀ r' : Localization.Away (r i * r j), Function.Surjective
        ((pullback.snd (fP i j) (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away (r i * r j)) (Localization.Away r'))))).appTop).hom := by
    intro i j
    letI : Algebra (B i) (Localization.Away (r i * r j)) := (ρ₁ i j).toRingHom.toAlgebra
    haveI : IsLocalization.Away (algebraMap S (B i) (r j)) (Localization.Away (r i * r j)) := hloc i j
    exact AlgebraicGeometry.Scheme.exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away
      (algebraMap S (B i) (r j)) (f' i) (e i) (he i) (hΓ i) (fP i j) (Limits.pullback.fst (ι i) (ι j)) (hsqP i j)
  choose eP heP1 heP3 heP5 heP6 using hE

  have hunit₂ : ∀ i j : Fin k, IsUnit (algebraMap S (Localization.Away (r i * r j)) (r j)) := by
    intro i j
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (r i * r j)) (r i * r j)
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let ρ₂ : ∀ i j : Fin k, B j →ₐ[S] Localization.Away (r i * r j) :=
    fun i j => R0Aux.liftAway (r j) (B j) (Localization.Away (r i * r j)) (hunit₂ i j)

  have hfover : ∀ i, ι i ≫ f = f' i ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))) := fun i => (hsq i).w
  have hρ₁S : ∀ i j, Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) := by
    intro i j
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun s => (ρ₁ i j).commutes s
  have hρ₂S : ∀ i j, Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B j))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) := by
    intro i j
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun s => (ρ₂ i j).commutes s

  have heP4 : ∀ i j, eP i j ≫ Limits.pullback.snd (ι i) (ι j) = Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ e j := by
    intro i j
    have w : (Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom) ≫ e i) ≫ ι i =
        (Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom) ≫ e j) ≫ ι j := by
      simpa only [Category.assoc] using heagree i j (Localization.Away (r i * r j)) (ρ₁ i j) (ρ₂ i j)
    have heq : eP i j = Limits.pullback.lift _ _ w := by
      apply (hsqP i j).hom_ext
      · rw [heP3, Limits.pullback.lift_fst]
      · rw [heP1]
        symm
        apply R0Aux.eq_of_comp_toSpec_eq (Submonoid.powers (r i * r j)) (Localization.Away (r i * r j))
        rw [Category.id_comp, Category.assoc, hoverP, Limits.pullback.lift_fst_assoc, Category.assoc, hfover,
          reassoc_of% (he i), hρ₁S]
    rw [heq, Limits.pullback.lift_snd]
  refine ⟨ρ₁, ρ₂, fP, eP, heP1, hoverP, heP3, heP4, heP5, heP6, ?_⟩

  intro i j l π₁₃ h₁ h₃
  obtain ⟨τ, fT, hlocT, hsqT, hoverT⟩ :=
    AlgebraicGeometry.Scheme.exists_isPullback_fst_fst_toSpecAway_of_charts_of_isPullback r B f f' ι hsq i j l

  obtain ⟨eT, heT1, heT3, heT5, -⟩ := by
    letI : Algebra (B i) (Localization.Away (r i * r j * r l)) := τ.toRingHom.toAlgebra
    haveI : IsLocalization.Away (algebraMap S (B i) (r j * r l)) (Localization.Away (r i * r j * r l)) := hlocT
    exact AlgebraicGeometry.Scheme.exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away
      (algebraMap S (B i) (r j * r l)) (f' i) (e i) (he i) (hΓ i) fT
      (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ≫ Limits.pullback.fst (ι i) (ι j)) hsqT

  set C3 := Localization.Away (r i * r j * r l) with hC3
  have hu : IsUnit (algebraMap S C3 (r i)) ∧ IsUnit (algebraMap S C3 (r j)) ∧ IsUnit (algebraMap S C3 (r l)) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := C3) (r i * r j * r l)
    rw [map_mul, map_mul] at h
    exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h), isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h),
      isUnit_of_mul_isUnit_right h⟩
  have hu12 : IsUnit (algebraMap S C3 (r i * r j)) := by rw [map_mul]; exact hu.1.mul hu.2.1
  have hu23 : IsUnit (algebraMap S C3 (r j * r l)) := by rw [map_mul]; exact hu.2.1.mul hu.2.2
  have hu13 : IsUnit (algebraMap S C3 (r i * r l)) := by rw [map_mul]; exact hu.1.mul hu.2.2
  let σ₁₂ : Localization.Away (r i * r j) →ₐ[S] C3 := R0Aux.liftAway (r i * r j) _ C3 hu12
  let σ₂₃ : Localization.Away (r j * r l) →ₐ[S] C3 := R0Aux.liftAway (r j * r l) _ C3 hu23
  let σ₁₃ : Localization.Away (r i * r l) →ₐ[S] C3 := R0Aux.liftAway (r i * r l) _ C3 hu13

  have hsub : ∀ (m : Fin k) (a b : B m →ₐ[S] C3), a = b := fun m a b =>
    (IsLocalization.algHom_subsingleton (Submonoid.powers (r m))).elim a b
  have hSpec_comp : ∀ (m : Fin k) {D : Type u} [CommRing D] [Algebra S D] (a : B m →ₐ[S] D) (b : D →ₐ[S] C3) (c : B m →ₐ[S] C3),
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) = Spec.map (CommRingCat.ofHom c.toRingHom) := by
    intro m D _ _ a b c
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (hsub m (b.comp a) c)
  have hσS : ∀ {D : Type u} [CommRing D] [Algebra S D] (b : D →ₐ[S] C3),
      Spec.map (CommRingCat.ofHom b.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S D)) =
        Spec.map (CommRingCat.ofHom (algebraMap S C3)) := by
    intro D _ _ b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun s => b.commutes s

  have hτS : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))) =
      Spec.map (CommRingCat.ofHom (algebraMap S C3)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun s => τ.commutes s
  have hbase : eT ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S C3)) := by
    rw [reassoc_of% heT3, hfover, reassoc_of% (he i), hτS]

  have hc : eT ≫ Limits.pullback.fst _ _ = Spec.map (CommRingCat.ofHom σ₁₂.toRingHom) ≫ eP i j := by
    apply (hsqP i j).hom_ext
    · rw [Category.assoc, heT3, Category.assoc, heP3, ← Category.assoc, hSpec_comp i (ρ₁ i j) σ₁₂ τ]
    · apply R0Aux.eq_of_comp_toSpec_eq (Submonoid.powers (r i * r j)) (Localization.Away (r i * r j))
      simp only [Category.assoc]
      rw [reassoc_of% (heP1 i j), hσS, hoverP, hbase]

  have hd : eT ≫ Limits.pullback.snd _ _ = Spec.map (CommRingCat.ofHom σ₂₃.toRingHom) ≫ eP j l := by
    apply (hsqP j l).hom_ext
    · rw [Category.assoc, ← Limits.pullback.condition, reassoc_of% hc, heP4, Category.assoc, heP3,
        ← Category.assoc, ← Category.assoc, hSpec_comp j (ρ₂ i j) σ₁₂ (σ₂₃.comp (ρ₁ j l)), hSpec_comp j (ρ₁ j l) σ₂₃ (σ₂₃.comp (ρ₁ j l))]
    · apply R0Aux.eq_of_comp_toSpec_eq (Submonoid.powers (r j * r l)) (Localization.Away (r j * r l))
      simp only [Category.assoc]
      rw [reassoc_of% (heP1 j l), hσS, hoverP, ← Limits.pullback.condition_assoc, ← Limits.pullback.condition_assoc]
      exact hbase

  have he' : eT ≫ π₁₃ = Spec.map (CommRingCat.ofHom σ₁₃.toRingHom) ≫ eP i l := by
    apply (hsqP i l).hom_ext
    · rw [Category.assoc, h₁, heT3, Category.assoc, heP3, ← Category.assoc, hSpec_comp i (ρ₁ i l) σ₁₃ τ]
    · apply R0Aux.eq_of_comp_toSpec_eq (Submonoid.powers (r i * r l)) (Localization.Away (r i * r l))
      simp only [Category.assoc]
      rw [reassoc_of% (heP1 i l), hσS, hoverP, reassoc_of% h₁]
      exact hbase
  exact ⟨fT, eT, σ₁₂, σ₂₃, σ₁₃, heT1, heT5, hc, hd, he'⟩

end S_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop (solution)
