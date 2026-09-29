-- Prove2me | solution 1 for Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/69111b6b-082e-5568-827f-964a0817149c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero

set_option autoImplicit false

open scoped MatrixGroups

namespace TwoResChars12

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    apply le_antisymm _ Ideal.le_jacobson
    intro n hn
    rw [Ideal.mem_bot]
    by_contra hn0

    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    haveI hprime : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := IsPrime.to_maximal_ideal hne
    have hmem : n ∈ Ideal.span {(p : ℤ)} := by
      have := (Ideal.mem_sInf.1 hn) (show Ideal.span {(p : ℤ)} ∈ {J : Ideal ℤ | ⊥ ≤ J ∧ J.IsMaximal} from ⟨bot_le, hmax⟩)
      exact this
    rw [Ideal.mem_span_singleton] at hmem
    have h1 : (p : ℤ).natAbs ≤ n.natAbs := Int.natAbs_le_of_dvd_ne_zero hmem hn0
    simp at h1
    omega
  · haveI : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_prime_natCast_eq_zero (K : Type) [Field K] [Algebra.FiniteType ℤ K] :
    ∃ p : ℕ, p.Prime ∧ (p : K) = 0 := by
  haveI := int_isJacobsonRing
  haveI hfin : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  haveI : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    rintro rfl
    haveI : CharZero K := CharP.charP_to_charZero K
    have hinj : Function.Injective (algebraMap ℤ K) := RingHom.injective_int _
    exact Int.not_isField ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  exact ⟨p, hpp, CharP.cast_eq_zero K p⟩

theorem exists_prime_natCast_mem (B : Type) [CommRing B] [Algebra.FiniteType ℤ B] (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ (p : B) ∈ 𝔪 := by
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hft : @Algebra.FiniteType ℤ (B ⧸ 𝔪) _ _ (Ideal.Quotient.algebra ℤ) := inferInstance
  obtain ⟨p, hpp, hp⟩ := @exists_prime_natCast_eq_zero (B ⧸ 𝔪) _ (by convert hft <;> rfl)
  refine ⟨p, hpp, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hp

end TwoResChars12

open TwoResChars12 in
theorem solution
    (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ 𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧
      (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ := by
  classical
  haveI := int_isJacobsonRing
  haveI hAJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ) (B := A)

  obtain ⟨𝔪₁, h𝔪₁⟩ := Ideal.exists_maximal A
  obtain ⟨p₁, hp₁, hp₁m⟩ := exists_prime_natCast_mem A 𝔪₁ h𝔪₁

  have hp₁0 : (p₁ : A) ≠ 0 := by exact_mod_cast hp₁.ne_zero
  let B := Localization.Away (p₁ : A)
  haveI : IsDomain B :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp₁0)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal B

  obtain ⟨h𝔪₂, hp₁not⟩ := (IsLocalization.isMaximal_iff_isMaximal_disjoint B (p₁ : A) 𝔫).1 h𝔫
  obtain ⟨p₂, hp₂, hp₂m⟩ := exists_prime_natCast_mem A (𝔫.under A) h𝔪₂
  have hne : p₁ ≠ p₂ := by
    rintro rfl
    exact hp₁not hp₂m
  exact ⟨p₁, p₂, 𝔪₁, 𝔫.under A, hp₁, hp₂, hne, h𝔪₁, h𝔪₂, hp₁m, hp₂m⟩

end S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero
end P2MW
export P2MW.S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero (solution)
