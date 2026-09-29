-- Prove2me | solution 1 for Algebra.TensorProduct.nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ea24a9cf-4f58-5aa4-ba1e-a2e303583fa0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace E160GC

open TensorProduct

theorem eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing {S : Type*} [CommRing S]
    [IsLocalRing S] (e : S) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    have h1 : 1 - e = 0 := (hu.mul_right_eq_zero).mp h0
    exact (sub_eq_zero.mp h1).symm
  · left
    exact (hu.mul_left_eq_zero).mp h0

theorem isLocalRing_of_surjective_of_isNilpotent {S T : Type*} [CommRing S] [CommRing T]
    [IsLocalRing T] (θ : S →+* T) (hθ : Function.Surjective θ)
    (hker : ∀ x, θ x = 0 → IsNilpotent x) : IsLocalRing S := by
  haveI : Nontrivial S := θ.domain_nontrivial
  have key : ∀ a : S, IsUnit (θ a) → IsUnit a := by
    intro a ha
    obtain ⟨c, hc⟩ := ha.exists_left_inv
    obtain ⟨b, rfl⟩ := hθ c
    have hn : IsNilpotent (b * a - 1) := hker _ (by rw [map_sub, map_mul, map_one, hc, sub_self])
    have hu : IsUnit (b * a - 1 + 1) := hn.isUnit_add_one
    rw [sub_add_cancel] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (θ a) with h | h
  · exact Or.inl (key a h)
  · refine Or.inr (key _ ?_)
    rwa [map_sub, map_one]

theorem isLocalRing_of_isArtinianRing_of_forall_isIdempotentElem {R : Type*} [CommRing R]
    [IsArtinianRing R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsLocalRing R := by
  obtain ⟨p, hpmax⟩ := Ideal.exists_maximal R
  haveI : p.IsPrime := hpmax.isPrime
  obtain ⟨r, hrp, hridem, hrq⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne p
  have hr1 : r = 1 := by
    rcases hR r hridem with h | h
    · exact absurd (h ▸ p.zero_mem : r ∈ p) hrp
    · exact h
  refine IsLocalRing.of_unique_max_ideal ⟨p, hpmax, fun q hq => ?_⟩
  by_contra hne
  have h1 : (1 : R) ∈ q := hr1 ▸ hrq q hq.isPrime hne
  exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr h1)

theorem isLocalRing_tensorProduct_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (K : Type u) [Field K] [Algebra k K] : IsLocalRing (K ⊗[k] R) := by
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : IsLocalRing R := isLocalRing_of_isArtinianRing_of_forall_isIdempotentElem hR
  set m : Ideal R := IsLocalRing.maximalIdeal R with hm
  have hmnil : IsNilpotent m := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

  haveI : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  haveI : Module.Finite k (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)
  let eκ : (R ⧸ m) ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij).symm

  let θ : K ⊗[k] R →ₐ[K] K ⊗[k] (R ⧸ m) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ k m)
  let eT : K ⊗[k] (R ⧸ m) ≃ₐ[K] K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eκ).trans
      (Algebra.TensorProduct.rid k K K)
  haveI : Nontrivial (K ⊗[k] (R ⧸ m)) := eT.symm.injective.nontrivial
  haveI : IsLocalRing (K ⊗[k] (R ⧸ m)) :=
    IsLocalRing.of_surjective' (eT.symm : K →+* K ⊗[k] (R ⧸ m)) eT.symm.surjective

  let g : R →ₗ[k] (R ⧸ m) := (Ideal.Quotient.mkₐ k m).toLinearMap
  let f : (m.restrictScalars k) →ₗ[k] R := (m.restrictScalars k).subtype
  have hg : Function.Surjective g := Ideal.Quotient.mkₐ_surjective k m
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr y.2
  have hexact := lTensor_exact K hfg hg
  have hθ_eq : ∀ x, θ x = LinearMap.lTensor K g x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r => simp [θ, g]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hθsurj : Function.Surjective θ := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective K hg y
    exact ⟨x, by rw [hθ_eq, hx]⟩
  have hker : ∀ x, θ x = 0 → IsNilpotent x := by
    intro x hx
    rw [hθ_eq] at hx
    obtain ⟨t, rfl⟩ := (hexact x).mp hx
    clear hx
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      have h1 : IsNilpotent ((1 : K) ⊗ₜ[k] (y : R)) := by
        obtain ⟨n, hn⟩ := hmnil
        refine ⟨n, ?_⟩
        have hy : (y : R) ^ n ∈ m ^ n := Ideal.pow_mem_pow y.2 n
        rw [hn] at hy
        have hy0 : (y : R) ^ n = 0 := by simpa using hy
        rw [Algebra.TensorProduct.tmul_pow, one_pow, hy0, TensorProduct.tmul_zero]
      have h2 : (a ⊗ₜ[k] (y : R) : K ⊗[k] R) = (a ⊗ₜ[k] (1 : R)) * ((1 : K) ⊗ₜ[k] (y : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [LinearMap.lTensor_tmul, f, Submodule.coe_subtype]
      rw [h2]
      exact (Commute.all _ _).isNilpotent_mul_left h1
    | add x y hx hy =>
      rw [map_add]
      exact (Commute.all _ _).isNilpotent_add hx hy
  exact isLocalRing_of_surjective_of_isNilpotent θ.toRingHom hθsurj hker

end E160GC

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial (K ⊗[k] R) ∧ ∀ e : K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  haveI := E160GC.isLocalRing_tensorProduct_of_isAlgClosed k R hR K
  exact ⟨inferInstance, fun e he =>
    E160GC.eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing e he⟩

end S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
end P2MW
export P2MW.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed (solution)
