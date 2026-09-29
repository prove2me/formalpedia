-- Prove2me | solution 1 for Algebra.exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/739845bf-cba5-56d1-ad0b-15e5107428f6

import Mathlib
import Theorems.Thm_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Algebra
p2m_export "Algebra" "commutes mk algebraMap mem_bot"
namespace MinimalCompare
p2m_open "Algebra"

open MvPolynomial

variable (k : Type*) [Field k] (e M : ℕ)

local notation "𝔫" => RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)

local notation "T" => MvPolynomial (Fin e) k ⧸ (𝔫) ^ (M + 1)

local notation "𝔱" => Ideal.map (Ideal.Quotient.mk ((𝔫) ^ (M + 1))) (𝔫)

theorem mem_ker_constantCoeff_iff (f : MvPolynomial (Fin e) k) : f ∈ (𝔫) ↔ MvPolynomial.constantCoeff f = 0 :=
  RingHom.mem_ker

theorem X_mem_ker_constantCoeff (j : Fin e) : (MvPolynomial.X j : MvPolynomial (Fin e) k) ∈ (𝔫) := by
  rw [RingHom.mem_ker, MvPolynomial.constantCoeff_X]

theorem ker_constantCoeff_eq_span : (𝔫) = Ideal.span (Set.range (MvPolynomial.X : Fin e → MvPolynomial (Fin e) k)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    rw [show Set.range (MvPolynomial.X : Fin e → MvPolynomial (Fin e) k) = MvPolynomial.X '' Set.univ by simp,
      MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      exact hm hf
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
    exact ⟨i, Set.mem_univ i, hi⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact X_mem_ker_constantCoeff k e j

theorem pow_eq_zero_of_mem (x : T) (hx : x ∈ (𝔱)) : x ^ (M + 1) = 0 := by
  have : x ^ (M + 1) ∈ ((𝔱) ^ (M + 1) : Ideal T) := Ideal.pow_mem_pow hx _
  rwa [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at this

theorem apply_mem_maximalIdeal {C : Type*} [CommRing C] [Algebra k C] [IsLocalRing C]
    (γ : T →ₐ[k] C) (x : T) (hx : x ∈ (𝔱)) : γ x ∈ IsLocalRing.maximalIdeal C := by
  have hnil : IsNilpotent (γ x) := ⟨M + 1, by rw [← map_pow, pow_eq_zero_of_mem k e M x hx, map_zero]⟩
  exact nilradical_le_prime (IsLocalRing.maximalIdeal C) (mem_nilradical.mpr hnil)

variable {k e M}

noncomputable def substAlgHom (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) : T →ₐ[k] T :=
  Ideal.Quotient.liftₐ ((𝔫) ^ (M + 1)) (MvPolynomial.aeval P) (by
    intro f hf

    have hmap' : ∀ g ∈ (𝔫), MvPolynomial.aeval P g ∈ (𝔱) := by
      intro g hg
      rw [ker_constantCoeff_eq_span k e] at hg
      induction hg using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; rw [MvPolynomial.aeval_X]; exact hP j
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx
    have hmap : Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin e) k →ₐ[k] T) (𝔫) ≤ (𝔱) :=
      Ideal.map_le_iff_le_comap.mpr fun g hg => hmap' g hg
    have : (MvPolynomial.aeval P) f ∈ Ideal.map (MvPolynomial.aeval P : MvPolynomial (Fin e) k →ₐ[k] T) ((𝔫) ^ (M + 1)) :=
      Ideal.mem_map_of_mem _ hf
    rw [Ideal.map_pow] at this
    have h2 := Ideal.pow_right_mono hmap (M + 1) this
    rwa [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot] at h2)

@[scoped simp] theorem substAlgHom_mk (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) (f : MvPolynomial (Fin e) k) :
    substAlgHom P hP (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P f := rfl

theorem substAlgHom_X (P : Fin e → T) (hP : ∀ j, P j ∈ (𝔱)) (j : Fin e) :
    substAlgHom P hP (Ideal.Quotient.mk _ (MvPolynomial.X j)) = P j := by
  rw [substAlgHom_mk, MvPolynomial.aeval_X]

end Algebra.MinimalCompare
p2m_reactivate "P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.Algebra P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.Algebra.MinimalCompare"
p2m_reactivate "P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.Algebra"

open Algebra.MinimalCompare in
theorem solution
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (e M : ℕ)
    (α β : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    (hαk : RingHom.ker α ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2)
    (hβk : RingHom.ker β ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2) :
    ∃ θ : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) ≃ₐ[k]
        (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)),
      β.comp (θ : _ →ₐ[k] _) = α := by
  classical
  have hβs : Function.Surjective (fun f : MvPolynomial (Fin e) k => β (Ideal.Quotient.mk _ f)) :=
    hβ.comp Ideal.Quotient.mk_surjective
  choose F hF using fun j : Fin e => hβs (α (Ideal.Quotient.mk _ (MvPolynomial.X j)))

  let G : Fin e → MvPolynomial (Fin e) k := fun j => F j - MvPolynomial.C (MvPolynomial.constantCoeff (F j))
  have hG : ∀ j, G j ∈ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) := fun j => by
    show F j - MvPolynomial.C (MvPolynomial.constantCoeff (F j)) ∈ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))
    rw [RingHom.mem_ker, map_sub, MvPolynomial.constantCoeff_C, sub_self]
  let P : Fin e → MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1) := fun j => Ideal.Quotient.mk _ (G j)
  have hP : ∀ j, P j ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1))) (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) := fun j => Ideal.mem_map_of_mem _ (hG j)
  have hXmem : ∀ j, Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) (MvPolynomial.X j) ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1))) (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) :=
    fun j => Ideal.mem_map_of_mem _ (X_mem_ker_constantCoeff k e j)

  have hβP : ∀ j, β (P j) = α (Ideal.Quotient.mk _ (MvPolynomial.X j)) := by
    intro j
    have hdec : β (P j) = α (Ideal.Quotient.mk _ (MvPolynomial.X j)) - algebraMap k C (MvPolynomial.constantCoeff (F j)) := by
      show β (Ideal.Quotient.mk _ (F j - MvPolynomial.C (MvPolynomial.constantCoeff (F j)))) = _
      rw [map_sub, map_sub, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
      exact congrArg (· - _) (hF j)
    have hc : algebraMap k C (MvPolynomial.constantCoeff (F j)) ∈ IsLocalRing.maximalIdeal C := by
      have : algebraMap k C (MvPolynomial.constantCoeff (F j)) = α (Ideal.Quotient.mk _ (MvPolynomial.X j)) - β (P j) := by
        rw [hdec]; ring
      rw [this]
      exact sub_mem (apply_mem_maximalIdeal k e M α _ (hXmem j)) (apply_mem_maximalIdeal k e M β _ (hP j))
    have hc0 : MvPolynomial.constantCoeff (F j) = 0 := by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).mp hc ((IsUnit.mk0 _ h).map (algebraMap k C))
    rw [hdec, hc0, map_zero, sub_zero]

  let θ := substAlgHom P hP
  have hβθ : β.comp θ = α := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    show β (θ (Ideal.Quotient.mk _ (MvPolynomial.X j))) = α (Ideal.Quotient.mk _ (MvPolynomial.X j))
    rw [substAlgHom_X]
    exact hβP j

  have hθ2 : ∀ j : Fin e, ∃ t, θ t - Ideal.Quotient.mk _ (MvPolynomial.X j) ∈
      (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1))) (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2 := by
    intro j
    obtain ⟨t, ht⟩ := hα (β (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    refine ⟨t, hβk ?_⟩
    rw [RingHom.mem_ker, map_sub, show β (θ t) = α t from congrArg (fun φ : _ →ₐ[k] C => φ t) hβθ, ht, sub_self]
  have hbij := MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq k e M θ hθ2
  exact ⟨AlgEquiv.ofBijective θ hbij, hβθ⟩

end S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated
end P2MW
export P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated (solution)
