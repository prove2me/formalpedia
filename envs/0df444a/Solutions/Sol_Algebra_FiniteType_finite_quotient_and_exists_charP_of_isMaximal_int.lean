-- Prove2me | solution 1 for Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c36fbeee-ab93-5c1b-b5fd-6d56ee0e8fbd

import Mathlib
import Theorems.Thm_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int

set_option autoImplicit false

namespace A3Aux

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_sInf_maximal]
  intro I hI
  by_cases h0 : I = ⊥
  · refine ⟨{J : Ideal ℤ | J.IsMaximal}, fun J hJ => Or.inl hJ, ?_⟩
    rw [h0]
    apply le_antisymm bot_le
    intro n hn
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := IsPrime.to_maximal_ideal hp0
    have hmem : n ∈ Ideal.span {(p : ℤ)} := (Submodule.mem_sInf.mp hn) _ hmax
    rw [Ideal.mem_span_singleton] at hmem
    have hdvd : p ∣ n.natAbs := Int.natCast_dvd.mp hmem
    have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hne
    have := Nat.le_of_dvd hpos hdvd
    omega
  · haveI := hI
    exact ⟨{I}, fun J hJ => Or.inl (by rw [Set.mem_singleton_iff.mp hJ]; exact IsPrime.to_maximal_ideal h0), by simp⟩

end A3Aux

theorem solution
    (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (𝔮 : Ideal A) [𝔮.IsMaximal] :
    Finite (A ⧸ 𝔮) ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ CharP (A ⧸ 𝔮) ℓ := by
  classical
  haveI := A3Aux.int_isJacobsonRing
  letI : Field (A ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  haveI : Algebra.FiniteType ℤ (A ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔮) (Ideal.Quotient.mkₐ_surjective ℤ 𝔮)
  have hfin := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ 𝔮)
  haveI := hfin
  haveI : Algebra.IsIntegral ℤ (A ⧸ 𝔮) := Algebra.IsIntegral.of_finite ℤ (A ⧸ 𝔮)

  let m0 : Ideal ℤ := (⊥ : Ideal (A ⧸ 𝔮)).comap (algebraMap ℤ (A ⧸ 𝔮))
  haveI hm0 : m0.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ) (⊥ : Ideal (A ⧸ 𝔮))
  have hm0ne : m0 ≠ ⊥ := by
    intro h
    have hbot : (⊥ : Ideal ℤ).IsMaximal := by rw [← h]; exact hm0
    have h2 : Ideal.span {(2 : ℤ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]; decide
    have h3 := hbot.eq_of_le h2 bot_le
    have : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := by rw [h3]; exact Ideal.subset_span rfl
    simp at this
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal m0).principal
  have hg0 : g ≠ 0 := by rintro rfl; apply hm0ne; rw [hg]; simp
  haveI : NeZero g.natAbs := ⟨Int.natAbs_ne_zero.mpr hg0⟩
  haveI : Finite (ℤ ⧸ m0) := by
    rw [show m0 = Ideal.span {g} from hg]
    exact Finite.of_equiv _ (Int.quotientSpanEquivZMod g).symm.toEquiv
  have hle : Ideal.map (algebraMap ℤ A) m0 ≤ 𝔮 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : algebraMap ℤ (A ⧸ 𝔮) x = 0 := by simpa [m0] using hx
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    rw [IsScalarTower.algebraMap_apply ℤ A (A ⧸ 𝔮)] at hx'
    exact hx'
  have hfinq : Finite (A ⧸ 𝔮) := Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient ℤ m0 A 𝔮 hle
  refine ⟨hfinq, ?_⟩
  haveI := hfinq
  obtain ⟨ℓ, hℓ⟩ := CharP.exists (A ⧸ 𝔮)
  haveI := hℓ
  exact ⟨ℓ, (CharP.char_is_prime_or_zero (A ⧸ 𝔮) ℓ).resolve_right (CharP.char_ne_zero_of_finite (A ⧸ 𝔮) ℓ), hℓ⟩

end S_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int
end P2MW
export P2MW.S_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int (solution)
