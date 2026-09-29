-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1be2da63-0cb1-5752-8f57-2411a1646cd7

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

namespace FBUnpackAux

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem one_comp_val {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    t ≫ (L.one (𝟙 _)).1 = (L.one t).1 :=
  congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))

theorem factorsThrough_one_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    FactorsThrough (L.one (𝟙 _)).1 P ↔ P = L.one t := by
  constructor
  · rintro ⟨P₀, h⟩
    have hP₀ : P₀ = t := by
      have h2 := P.2
      rw [← h, Category.assoc, (L.one _).2, Category.comp_id] at h2
      exact h2
    apply Subtype.ext
    rw [← h, hP₀, one_comp_val]
  · intro h
    subst h
    exact ⟨t, one_comp_val L t⟩

theorem inv_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : L.inv t (L.one t) = L.one t := by
  have h := L.inv_mul_cancel t (L.one t)
  rw [L.mul_one] at h
  exact h

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem pushPt_one (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pushPt φ hφ (L.one t) = L.one t := by
  apply eq_one_of_mul_self
  have h := hhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact h.symm

end FBUnpackAux

open FBUnpackAux in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X),
        ∃ u : FakeEllipticCurve.WithFullLevel Λ 1 m S, s.Packages u := by
  classical
  intro X s
  haveI : NeZero m := ⟨by omega⟩
  haveI : IsProper X.f := X.bundle.proper
  have hβgen : ∀ x : ↥Λ, ∃ n : Fin 4 → ℤ, x = ∑ i, n i • β i := fun x => (hβ x).exists
  have hβind : ∀ n : Fin 4 → ℤ, ∑ i, n i • β i = 0 → n = 0 := by
    intro n hn
    exact (hβ 0).unique (by rw [hn]) (by simp)

  have hsec : (X.L.one (𝟙 _)).1 ≫ X.f = 𝟙 _ := (X.L.one (𝟙 _)).2
  haveI : IsClosedImmersion ((X.L.one (𝟙 _)).1 ≫ X.f) := by rw [hsec]; infer_instance
  haveI : IsFinite ((X.L.one (𝟙 _)).1 ≫ X.f) := by rw [hsec]; infer_instance
  haveI : Flat ((X.L.one (𝟙 _)).1 ≫ X.f) := by rw [hsec]; infer_instance
  haveI : LocallyOfFinitePresentation ((X.L.one (𝟙 _)).1 ≫ X.f) := by rw [hsec]; infer_instance
  haveI : IsIso ((X.L.one (𝟙 _)).1 ≫ X.f) := by rw [hsec]; infer_instance
  let E : FakeEllipticCurve Λ 1 S :=
    { A := X.A, f := X.f, L := X.L, comm := X.comm, bundle := X.bundle
      dim_fibre := fun p => by rw [X.dim_fibre p]; rfl
      act := s.act, act_over := s.act_over, act_hom := s.act_hom, act_one := s.act_one, act_mul := s.act_mul
      act_add := s.act_add, act_trace := s.act_trace
      C := Spec (CommRingCat.of S), lev := (X.L.one (𝟙 _)).1
      lev_closed := IsClosedImmersion.of_comp (X.L.one (𝟙 _)).1 X.f
      lev_sub := by
        intro T t P Q hP hQ
        rw [factorsThrough_one_iff] at hP hQ
        subst hP; subst hQ
        exact ⟨(factorsThrough_one_iff X.L t _).mpr (X.L.one_mul t _), (factorsThrough_one_iff X.L t _).mpr (inv_one X.L t)⟩
      lev_one := by
        intro T t
        exact (factorsThrough_one_iff X.L t _).mpr rfl
      lev_torsion := by
        intro T t P hP
        rw [factorsThrough_one_iff] at hP
        subst hP
        show X.L.mul t (X.L.one t) (X.L.one t) = X.L.one t
        exact X.L.one_mul t _
      lev_stable := fun x => by
        intro T t P hP
        rw [factorsThrough_one_iff] at hP ⊢
        subst hP
        exact pushPt_one X.L (s.act x) (s.act_over x) (fun t P Q => s.act_hom x t P Q) t
      lev_finite := inferInstance, lev_flat := inferInstance, lev_finitePresentation := inferInstance
      lev_rank := fun p => by rw [Scheme.Hom.finrank_eq_one_of_isIso]; simp
      lev_fibre := fun k _ _ sk _ => by
        refine ⟨⟨fun _ => ⟨X.L.one _, (factorsThrough_one_iff X.L _ _).mpr rfl⟩, fun _ => 0,
          fun x => Subsingleton.elim _ _, fun P => Subtype.ext ((factorsThrough_one_iff X.L _ _).mp P.2).symm⟩, ?_⟩
        intro x y
        exact (X.L.one_mul _ _).symm }

  have hQ := CerednikDrinfeld.QM.FakeEllipticCurve.nsmulPt_eq_one_and_torsionBasis_of_nsmul_eq_one_of_finComb
    E m X.P X.P_torsion X.P_indep X.P_span
  obtain ⟨FL, hFL⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_of_torsionBasis_eq_pushPt_act hΛ.1 E m β hβgen hβind
    X.P s.P (fun i => (s.level_match i).symm) hQ
  refine ⟨⟨E, FL⟩, Iso.refl _, Category.id_comp _, ?_, ?_, ?_⟩
  · intro T t x y
    have hx : (⟨x.1 ≫ (Iso.refl X.A).hom, by rw [Iso.refl_hom, Category.assoc, Category.id_comp]; exact x.2⟩ : SchemeHomOver t X.f) = x :=
      Subtype.ext (Category.comp_id _)
    have hy : (⟨y.1 ≫ (Iso.refl X.A).hom, by rw [Iso.refl_hom, Category.assoc, Category.id_comp]; exact y.2⟩ : SchemeHomOver t X.f) = y :=
      Subtype.ext (Category.comp_id _)
    change (X.L.mul t x y).1 ≫ 𝟙 _ = (X.L.mul t _ _).1
    rw [Category.comp_id, hx, hy]
  · intro x
    change s.act x ≫ 𝟙 _ = 𝟙 _ ≫ s.act x
    rw [Category.comp_id, Category.id_comp]
  · change FL.P.1 ≫ 𝟙 _ = s.P.1
    rw [Category.comp_id, hFL]

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages (solution)
