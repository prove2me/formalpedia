-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.withFullLevel_isPullback_of_packages_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7dd56572-bb45-51a3-9aa6-5292be2e1a69

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_withFullLevel_isPullback_of_packages_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

namespace FBBC

theorem main
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    (m : ℕ) (S : Type) [CommRing S]
    (S' : Type) [CommRing S'] (φ : S →+* S')
    (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
    (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X')
    (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m S')
    (hu : s.Packages u) (hu' : s'.Packages u') (hpb : QMStructure.IsPullback φ s s') :
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by
  obtain ⟨e, he, hemul, heact, heP⟩ := hu
  obtain ⟨e', he', he'mul, he'act, he'P⟩ := hu'
  obtain ⟨gA, hg, hgmul, -, -, hgact, hgP⟩ := hpb
  have hei : e.inv ≫ u.1.f = X.f := by rw [← he, Iso.inv_hom_id_assoc]
  have hei' : e'.inv ≫ u'.1.f = X'.f := by rw [← he', Iso.inv_hom_id_assoc]

  let g : u'.1.A ⟶ u.1.A := e'.hom ≫ gA ≫ e.inv
  have hgcart : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ)) := by
    refine hg.of_iso e'.symm e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [g]
    · simp [hei']
    · simp [hei]
    · simp

  have heinv : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t X.f),
      (X.L.mul t x y).1 ≫ e.inv =
        (u.1.L.mul t ⟨x.1 ≫ e.inv, by rw [Category.assoc, hei]; exact x.2⟩
          ⟨y.1 ≫ e.inv, by rw [Category.assoc, hei]; exact y.2⟩).1 := by
    intro T t x y
    have h := hemul t ⟨x.1 ≫ e.inv, by rw [Category.assoc, hei]; exact x.2⟩ ⟨y.1 ≫ e.inv, by rw [Category.assoc, hei]; exact y.2⟩
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    rw [← cancel_mono e.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact h.symm
  refine ⟨g, hgcart, ?_, ?_, ?_, ?_⟩
  ·
    intro T t' P Q
    simp only [g, ← Category.assoc]
    rw [he'mul, hgmul, heinv]
  ·
    intro x
    have hia : s.act x ≫ e.inv = e.inv ≫ u.1.act x := by
      rw [← cancel_epi e.hom, ← Category.assoc, ← heact x, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    show u'.1.act x ≫ e'.hom ≫ gA ≫ e.inv = (e'.hom ≫ gA ≫ e.inv) ≫ u.1.act x
    rw [← Category.assoc (u'.1.act x), he'act x, Category.assoc, ← Category.assoc (s'.act x), hgact x,
      Category.assoc, hia]
    simp only [Category.assoc]
  ·
    intro T t' P hP
    have hP1 : P = u'.1.L.one t' := by
      have := u'.1.lev_torsion t' P hP
      change u'.1.L.mul t' (u'.1.L.one t') P = u'.1.L.one t' at this
      rwa [u'.1.L.one_mul] at this
    subst hP1

    obtain ⟨P₀, hP₀⟩ := u.1.lev_one (t' ≫ Spec.map (CommRingCat.ofHom φ))
    refine ⟨P₀, ?_⟩
    rw [hP₀]

    letI := u'.1.L.pointGroup t'
    letI := u.1.L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
    let Φ : SchemeHomOver t' u'.1.f → SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) u.1.f :=
      fun x => ⟨x.1 ≫ g, by rw [Category.assoc, hgcart.w, ← Category.assoc, x.2]⟩
    have hΦ : ∀ x y, Φ (x * y) = Φ x * Φ y := by
      intro x y
      apply Subtype.ext
      change (u'.1.L.mul t' x y).1 ≫ g = (u.1.L.mul _ ⟨x.1 ≫ g, _⟩ ⟨y.1 ≫ g, _⟩).1
      simp only [g, ← Category.assoc]
      rw [he'mul, hgmul, heinv]
    have h1 := (MonoidHom.mk' Φ hΦ).map_one
    exact (congrArg Subtype.val h1).symm
  ·
    simp only [g]
    rw [← Category.assoc, he'P, ← Category.assoc, hgP, Category.assoc]
    congr 1
    rw [← cancel_mono e.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, heP]

end FBBC

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
        (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X')
        (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m S'),
        s.Packages u → s'.Packages u' → QMStructure.IsPullback φ s s' →
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' :=
  fun S' _ φ X X' s s' u u' hu hu' hpb => FBBC.main Λ star β m S S' φ X X' s s' u u' hu hu' hpb

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_withFullLevel_isPullback_of_packages_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_withFullLevel_isPullback_of_packages_of_isPullback (solution)
