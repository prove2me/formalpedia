-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c90cb095-57af-5f81-a977-a901f8c85aee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace CharZeroGenerization

theorem exists_ringHom_field_charZero {A : Type u} [CommRing A] [IsLocalRing A] (n : ℕ)
    (hn : (n : A) ∈ IsLocalRing.maximalIdeal A) (hnil : ¬ IsNilpotent (n : A)) :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K), Nonempty (A →+* K) := by
  classical

  have hP : ∃ P : Ideal A, P.IsPrime ∧ (n : A) ∉ P := by
    by_contra h
    push Not at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  obtain ⟨P, hPprime, hnP⟩ := hP
  haveI := hPprime
  let K := FractionRing (A ⧸ P)
  let f : A →+* K := (algebraMap (A ⧸ P) K).comp (Ideal.Quotient.mk P)
  have hf_ker : ∀ a : A, f a = 0 → a ∈ P := by
    intro a ha
    have : (Ideal.Quotient.mk P a : A ⧸ P) = 0 := by
      apply IsFractionRing.injective (A ⧸ P) K
      simpa [f] using ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  refine ⟨K, inferInstance, ?_, ⟨f⟩⟩

  haveI := ringChar.charP K
  obtain hprime | hzero := CharP.char_is_prime_or_zero K (ringChar K)
  · exfalso
    set ℓ := ringChar K with hℓ
    have hℓK : (ℓ : K) = 0 := by simp
    have hℓP : (ℓ : A) ∈ P := hf_ker _ (by simp)
    have hℓm : (ℓ : A) ∈ IsLocalRing.maximalIdeal A :=
      IsLocalRing.le_maximalIdeal hPprime.ne_top hℓP
    by_cases hdvd : ℓ ∣ n
    · obtain ⟨c, rfl⟩ := hdvd
      exact hnP (by simpa [Nat.cast_mul] using P.mul_mem_right (c : A) hℓP)
    · have hcop : Nat.Coprime ℓ n := (Nat.coprime_or_dvd_of_prime hprime n).resolve_right hdvd
      have hcopA : IsCoprime (ℓ : A) (n : A) := by
        simpa using (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom A)
      obtain ⟨a, b, hab⟩ := hcopA
      have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        rw [← hab]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓm) (Ideal.mul_mem_left _ _ hn)
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · haveI : CharP K 0 := hzero ▸ ringChar.charP K
    exact CharP.charP_to_charZero K

end CharZeroGenerization

open CharZeroGenerization

theorem solution
    {X : Scheme.{u}} (x : X) (n : ℕ)
    (hn : ((n : ℕ) : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hnil : ¬ IsNilpotent ((n : ℕ) : X.presheaf.stalk x)) :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K) (ξ : Spec (CommRingCat.of K) ⟶ X),
      ∀ z : Spec (CommRingCat.of K), ξ.base z ⤳ x := by
  obtain ⟨K, _, _, ⟨f⟩⟩ := exists_ringHom_field_charZero (A := X.presheaf.stalk x) n hn hnil
  refine ⟨K, inferInstance, inferInstance, Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x, fun z => ?_⟩
  have hz : (Spec.map (CommRingCat.ofHom f) ≫ X.fromSpecStalk x).base z ∈ Set.range (X.fromSpecStalk x).base :=
    ⟨(Spec.map (CommRingCat.ofHom f)).base z, by simp⟩
  rw [Scheme.range_fromSpecStalk] at hz
  exact hz

end S_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent (solution)
