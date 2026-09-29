-- Prove2me | solution 1 for AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/127836bf-7b16-5b9e-8905-8d5ab9c91bb8

import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective

set_option autoImplicit false

universe u

namespace DilatationQuotient

open AffineDilatation

variable {R : Type u} [CommRing R] (π : R)
  {C : Type u} (A : Type u) [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]

local notation "a" => algebraMap R C π
local notation "a'" => algebraMap R A π
local notation "q" => algebraMap C A
local notation "LC" => Localization.Away (algebraMap R C π)
local notation "LA" => Localization.Away (algebraMap R A π)

theorem q_a : q a = a' := (IsScalarTower.algebraMap_apply R C A π).symm

noncomputable def Φ : LC →ₐ[C] LA :=
  IsLocalization.liftAlgHom (M := Submonoid.powers a) (f := Algebra.ofId C LA) (fun y => by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    change IsUnit (algebraMap C LA y)
    rw [← hn, map_pow, IsScalarTower.algebraMap_apply C A LA, q_a π A]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (S := LA) (algebraMap R A π)))

theorem Φ_algebraMap (c : C) : Φ π A (algebraMap C LC c) = algebraMap A LA (q c) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply C A LA]

theorem Φ_mk' (c : C) (n : ℕ) :
    Φ π A (IsLocalization.mk' LC c (⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers a)) =
      IsLocalization.mk' LA (q c) (⟨a' ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers a') := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have h : IsLocalization.mk' LC c (⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers a) * algebraMap C LC (a ^ n) =
      algebraMap C LC c := IsLocalization.mk'_spec LC c ⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩
  have h2 := congrArg (Φ π A) h
  rw [map_mul, Φ_algebraMap, Φ_algebraMap, map_pow, q_a π A] at h2
  rw [← h2]

theorem Φ_mem_subalgebra (J : Ideal C) (x : LC) (hx : x ∈ subalgebra J a) :
    Φ π A x ∈ subalgebra (J.map q) a' := by
  have hle : (subalgebra J a).map (Φ π A) ≤ (subalgebra (J.map q) a').restrictScalars C := by
    rw [subalgebra_eq_adjoin, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    change Φ π A _ ∈ subalgebra (J.map q) a'
    have : Φ π A (IsLocalization.mk' LC g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) =
        IsLocalization.mk' LA (q g) (⟨a', Submonoid.mem_powers a'⟩ : Submonoid.powers a') := by
      have h := Φ_mk' π A g 1
      simp only [pow_one] at h
      exact h
    rw [this]
    exact gen_subset _ _ ⟨q g, Ideal.mem_map_of_mem _ hg, rfl⟩
  exact hle ⟨x, hx, rfl⟩

noncomputable def θ (J : Ideal C) :
    AffineDilatation.Ring J a →ₐ[C] AffineDilatation.Ring (J.map q) a' where
  toFun x := ⟨Φ π A x.1, Φ_mem_subalgebra π A J x.1 x.2⟩
  map_one' := Subtype.ext (by change Φ π A 1 = 1; exact map_one _)
  map_mul' x y := Subtype.ext (by change Φ π A (x.1 * y.1) = Φ π A x.1 * Φ π A y.1; exact map_mul _ _ _)
  map_zero' := Subtype.ext (by change Φ π A 0 = 0; exact map_zero _)
  map_add' x y := Subtype.ext (by change Φ π A (x.1 + y.1) = Φ π A x.1 + Φ π A y.1; exact map_add _ _ _)
  commutes' c := Subtype.ext (by
    change Φ π A (algebraMap C LC c) = algebraMap C LA c
    exact AlgHom.commutes _ _)

theorem coe_θ (J : Ideal C) (x : AffineDilatation.Ring J a) : ((θ π A J x : AffineDilatation.Ring (J.map q) a') : LA) = Φ π A x.1 := rfl

theorem θ_surjective (J : Ideal C) (hsurj : Function.Surjective q) : Function.Surjective (θ π A J) := by
  intro y

  suffices h : ∀ z : LA, z ∈ subalgebra (J.map q) a' → ∃ x : AffineDilatation.Ring J a, Φ π A x.1 = z by
    obtain ⟨x, hx⟩ := h y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  intro z hz
  rw [subalgebra_eq_adjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨h, hh, rfl⟩ := hz
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective q hsurj).mp hh
    refine ⟨divElem J a g hg, ?_⟩
    have h := Φ_mk' π A g 1
    simp only [pow_one] at h
    exact h
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := hsurj r
    exact ⟨algebraMap C _ c, Φ_algebraMap π A c⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [← hx', ← hy']; exact map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
    exact ⟨x' * y', by rw [← hx', ← hy']; exact map_mul _ _ _⟩

theorem θ_eq_zero_iff (J : Ideal C) (x : AffineDilatation.Ring J a) :
    θ π A J x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
      (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)) := by
  constructor
  · intro h0
    have h0' : Φ π A x.1 = 0 := by
      have := congrArg Subtype.val h0
      exact this

    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x.1
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs : s = ⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩ := Subtype.ext hm.symm
    subst hs
    simp only at hcs
    rw [← hcs, Φ_mk', IsLocalization.mk'_eq_zero_iff] at h0'
    obtain ⟨⟨t, ht⟩, hct⟩ := h0'
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp ht

    have hker : a ^ k * c ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul, map_pow, q_a π A, hk]
      exact hct
    refine ⟨m + k, ?_⟩
    have heq : (algebraMap R (AffineDilatation.Ring J a) π) ^ (m + k) * x =
        algebraMap C (AffineDilatation.Ring J a) (a ^ k * c) := by
      apply Subtype.ext
      change (algebraMap R LC π) ^ (m + k) * x.1 = algebraMap C LC (a ^ k * c)
      have hspec : algebraMap C LC (a ^ m) *
          IsLocalization.mk' LC c (⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩ : Submonoid.powers a) =
          algebraMap C LC c :=
        IsLocalization.mk'_spec' LC c ⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩
      rw [IsScalarTower.algebraMap_apply R C LC, ← map_pow, add_comm, pow_add, map_mul, mul_assoc, ← hcs, hspec,
        ← map_mul]
    rw [heq]
    exact Ideal.mem_map_of_mem _ hker
  · rintro ⟨ν, hν⟩

    have hkill : ∀ y ∈ (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)), θ π A J y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        rw [AlgHom.commutes]
        apply Subtype.ext
        change algebraMap C LA i = 0
        rw [IsScalarTower.algebraMap_apply C A LA, RingHom.mem_ker.mp hi, map_zero]
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [smul_eq_mul, map_mul, hy, mul_zero]
    have h := hkill _ hν
    rw [map_mul, map_pow] at h

    have hunit : IsUnit ((θ π A J) (algebraMap R (AffineDilatation.Ring J a) π) : AffineDilatation.Ring (J.map q) a').1 := by
      rw [coe_θ]
      change IsUnit (Φ π A (algebraMap R LC π))
      rw [IsScalarTower.algebraMap_apply R C LC, Φ_algebraMap, q_a π A]
      exact IsLocalization.Away.algebraMap_isUnit (S := LA) (algebraMap R A π)
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    change (((θ π A J) (algebraMap R _ π)).1) ^ ν * (θ π A J x).1 = 0 at h'
    exact (hunit.pow ν).mul_right_eq_zero.mp h'

theorem main (hsurj : Function.Surjective q) (J : Ideal C) :
    ∃ θ' : AffineDilatation.Ring J a →ₐ[C] AffineDilatation.Ring (J.map q) a',
      Function.Surjective θ' ∧
      ∀ x : AffineDilatation.Ring J a,
        θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
          (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)) :=
  ⟨θ π A J, θ_surjective π A J hsurj, θ_eq_zero_iff π A J⟩

end DilatationQuotient

theorem solution
    {R : Type u} [CommRing R] (π : R)
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A)) (J : Ideal C) :
    ∃ θ' : AffineDilatation.Ring J (algebraMap R C π) →ₐ[C]
        AffineDilatation.Ring (J.map (algebraMap C A)) (algebraMap R A π),
      Function.Surjective θ' ∧
      ∀ x : AffineDilatation.Ring J (algebraMap R C π),
        θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
          (RingHom.ker (algebraMap C A)).map (algebraMap C (AffineDilatation.Ring J (algebraMap R C π))) :=
  DilatationQuotient.main π A hsurj J

end S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective
end P2MW
export P2MW.S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective (solution)
