-- Prove2me | solution 1 for AlgebraicGeometry.base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/96c4c972-a40b-5539-aa68-e67eec3c6a2c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin

set_option autoImplicit false

namespace Ws23
namespace FrobTop

noncomputable def powHom (p : ℕ) (hp : p.Prime) (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' x y := by
    rw [add_pow_prime_eq hp, h]
    simp

theorem powHom_apply (p : ℕ) (hp : p.Prime) (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p hp R h x = x ^ p := rfl

theorem isIntegral_powHom (p : ℕ) (hp : p.Prime) (R : Type*) [CommRing R] (h : (p : R) = 0) :
    (powHom p hp R h).IsIntegral := fun b =>
  ⟨Polynomial.X ^ p - Polynomial.C b, Polynomial.monic_X_pow_sub_C b hp.ne_zero, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, powHom_apply]⟩

theorem finite_powHom_of_finiteType (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R]
    (ψ : ZMod p →+* R) (hψ : ψ.FiniteType) (h : (p : R) = 0) : (powHom p hp.out R h).Finite := by
  refine RingHom.Finite.of_isIntegral_of_finiteType (isIntegral_powHom p hp.out R h) ?_
  refine RingHom.FiniteType.of_comp_finiteType (f := ψ) ?_
  have : (powHom p hp.out R h).comp ψ = ψ := by
    ext x
    simp [powHom_apply, ← map_pow, ZMod.pow_card]
  rw [this]
  exact hψ

end Ws23.FrobTop

namespace Ws23
namespace FrobTop

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem natCast_eq_zero_of_hom (p : ℕ) {A C : Type*} [CommRing A] [CommRing C] (θ : A →+* C) (h : (p : A) = 0) :
    (p : C) = 0 := by
  rw [← map_natCast θ p, h, map_zero]

theorem specMap_base_apply_of_pow (p : ℕ) (hp : p.Prime) {R : CommRingCat.{0}} (u : R ⟶ R)
    (hu : ∀ a, u.hom a = a ^ p) (y : Spec R) : (Spec.map u).base y = y := by
  rw [Spec.map_base]
  show PrimeSpectrum.comap u.hom y = y
  ext a
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hu]
  exact ⟨fun ha => y.2.mem_of_pow_mem p ha, fun ha => Ideal.pow_mem_of_mem _ ha p hp.pos⟩

theorem main (p : ℕ) [hp : Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p)))
    [LocallyOfFiniteType f] (F : X ⟶ X) (hFb : F ≫ f = f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F) :
    (∀ x : X, F.base x = x) ∧ Surjective F ∧ QuasiCompact F ∧ LocallyQuasiFinite F ∧ IsAffineHom F ∧ IsFinite F := by
  classical
  let 𝒰 := X.affineCover
  let R : 𝒰.I₀ → CommRingCat.{0} := fun j => (X.local_affine j).choose_spec.choose
  let ιj : ∀ j, Spec (R j) ⟶ X := fun j => 𝒰.f j
  haveI hopen : ∀ j, IsOpenImmersion (ιj j) := fun j => inferInstanceAs (IsOpenImmersion (𝒰.f j))
  let ψ : ∀ j, CommRingCat.of (ZMod p) ⟶ R j := fun j => Spec.preimage (ιj j ≫ f)
  have hψ : ∀ j, Spec.map (ψ j) = ιj j ≫ f := fun j => Spec.map_preimage _
  have hpR : ∀ j, (p : R j) = 0 := fun j => natCast_eq_zero_of_hom p (ψ j).hom (ZMod.natCast_self p)
  let φ : ∀ j, R j ⟶ R j := fun j => CommRingCat.ofHom (powHom p hp.out (R j) (hpR j))

  have hpin : ∀ j, ιj j ≫ F = Spec.map (φ j) ≫ ιj j := by
    intro j
    by_cases hR : Nontrivial (R j)
    · let alg : Algebra (ZMod p) (R j) := (ψ j).hom.toAlgebra
      have hchar : CharP (R j) p :=
        charP_of_injective_algebraMap (@algebraMap (ZMod p) (R j) _ _ alg).injective p
      have hx : ιj j ≫ f = Spec.map (CommRingCat.ofHom (@algebraMap (ZMod p) (R j) _ _ alg)) := by
        rw [show @algebraMap (ZMod p) (R j) _ _ alg = (ψ j).hom from rfl, CommRingCat.ofHom_hom, hψ]
      have h1 := @hF (R j) _ alg hchar (ιj j) hx
      have hφ : CommRingCat.ofHom (@frobenius (R j) _ p (ExpChar.prime hp.out)) = φ j := by
        apply CommRingCat.hom_ext
        ext a
        rw [CommRingCat.hom_ofHom, frobenius_def]
        rfl
      have h1' : Spec.map (φ j) ≫ ιj j = ιj j ≫ F := by
        rw [← hφ]
        convert h1
      exact h1'.symm
    · haveI : Subsingleton (R j) := not_nontrivial_iff_subsingleton.mp hR
      haveI : IsEmpty ↥(Spec (R j)) := by
        show IsEmpty (PrimeSpectrum (R j))
        infer_instance
      exact (isInitialOfIsEmpty (X := Spec (R j))).hom_ext _ _

  have hbase : ∀ x : X, F.base x = x := by
    intro x
    obtain ⟨j, y, rfl⟩ := 𝒰.exists_eq x
    have h := congrArg (fun g : Spec (R j) ⟶ X => g.base y) (hpin j)
    simp only at h
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app,
      specMap_base_apply_of_pow p hp.out (φ j) (fun _ => rfl)] at h
    exact h

  have hfin : IsFinite F := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun j => ?_
    have hrange : F ⁻¹ᵁ (ιj j).opensRange = (ιj j).opensRange := by
      ext x
      simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe]

      rw [hbase]
    have hsq : IsPullback (Spec.map (φ j)) (ιj j) (ιj j) F :=
      IsOpenImmersion.isPullback _ _ _ _ (hpin j) hrange
    have e := hsq.flip.isoPullback_hom_snd
    have hft : (ψ j).hom.FiniteType := by
      have : LocallyOfFiniteType (Spec.map (ψ j)) := by rw [hψ]; infer_instance
      exact HasRingHomProperty.Spec_iff.1 this
    have hSpecFin : IsFinite (Spec.map (φ j)) :=
      (IsFinite.SpecMap_iff _).2 (finite_powHom_of_finiteType p (R j) (ψ j).hom hft (hpR j))
    rw [← e] at hSpecFin
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).1 hSpecFin
  haveI := hfin
  exact ⟨hbase, ⟨fun x => ⟨x, hbase x⟩⟩, inferInstance, inferInstance, inferInstance, hfin⟩

end Ws23.FrobTop

open CategoryTheory AlgebraicGeometry

theorem solution
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (ZMod p))) [LocallyOfFiniteType f]
    (F : X ⟶ X) (hFb : F ≫ f = f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)) →
        Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x = x ≫ F) :
    (∀ x : X, F.base x = x) ∧ Surjective F ∧ QuasiCompact F ∧ LocallyQuasiFinite F ∧ IsAffineHom F ∧ IsFinite F :=
  Ws23.FrobTop.main p f F hFb hF

end S_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin
end P2MW
export P2MW.S_AlgebraicGeometry_base_apply_eq_and_surjective_and_locallyQuasiFinite_and_isFinite_of_frobenius_pin (solution)
