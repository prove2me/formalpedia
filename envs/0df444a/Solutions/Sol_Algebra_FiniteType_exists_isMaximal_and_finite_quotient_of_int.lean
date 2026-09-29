-- Prove2me | solution 1 for Algebra.FiniteType.exists_isMaximal_and_finite_quotient_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/55bf0b21-b841-5410-b9dd-c923b6221be5

import Mathlib
import Theorems.Thm_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int

set_option autoImplicit false

namespace FinResBody

scoped instance : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    refine le_antisymm (fun n hn => ?_) Ideal.le_jacobson
    rw [Ideal.jacobson, Ideal.mem_sInf] at hn
    by_contra hne
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    haveI := Fact.mk hp
    have hmax : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hmem := hn ⟨bot_le, hmax⟩
    rw [Ideal.mem_span_singleton] at hmem
    have h1 : (p : ℤ).natAbs ∣ n.natAbs := Int.natAbs_dvd_natAbs.2 hmem
    rw [Int.natAbs_natCast] at h1
    have h2 : n.natAbs ≠ 0 := by rwa [ne_eq, Int.natAbs_eq_zero]
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  · have hmax : P.IsMaximal := hP.isMaximal hbot
    refine le_antisymm (sInf_le ⟨le_rfl, hmax⟩) Ideal.le_jacobson

end FinResBody
p2m_reactivate "P2MW.S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int.FinResBody"

open FinResBody in
theorem solution
    (R : Type) [CommRing R] [Algebra ℤ R] [Nontrivial R] [Algebra.FiniteType ℤ R] :
    ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ Finite (R ⧸ 𝔪) := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  refine ⟨𝔪, h𝔪, ?_⟩
  haveI := h𝔪
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  letI instAlg : Algebra ℤ (R ⧸ 𝔪) := Ideal.Quotient.algebra ℤ
  letI instMod : Module ℤ (R ⧸ 𝔪) := Algebra.toModule

  haveI : Algebra.FiniteType ℤ (R ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔪) (Ideal.Quotient.mkₐ_surjective ℤ 𝔪)
  haveI hfin : Module.Finite ℤ (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ 𝔪)
  haveI : Algebra.IsIntegral ℤ (R ⧸ 𝔪) := @Algebra.IsIntegral.of_finite ℤ (R ⧸ 𝔪) _ _ _ hfin

  let P : Ideal ℤ := 𝔪.comap (algebraMap ℤ R)
  have hPeq : P = (⊥ : Ideal (R ⧸ 𝔪)).comap (algebraMap ℤ (R ⧸ 𝔪)) := by
    rw [show algebraMap ℤ (R ⧸ 𝔪) = (Ideal.Quotient.mk 𝔪).comp (algebraMap ℤ R) from rfl, ← Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  haveI hPmax : P.IsMaximal := by
    rw [hPeq]; exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ) (⊥ : Ideal (R ⧸ 𝔪))

  have hPne : P ≠ ⊥ := by
    intro hP
    have h2 : (Ideal.span {(2 : ℤ)} : Ideal ℤ) = ⊤ := by
      refine (hP ▸ hPmax).1.2 _ ?_
      rw [bot_lt_iff_ne_bot, ne_eq, Ideal.span_singleton_eq_bot]; norm_num
    rw [Ideal.span_singleton_eq_top] at h2
    exact absurd (Int.isUnit_iff.1 h2) (by norm_num)
  haveI : Finite (ℤ ⧸ P) := by
    obtain ⟨g, hg⟩ : ∃ g : ℤ, P = Ideal.span {g} := ⟨_, ((IsPrincipalIdealRing.principal P).span_singleton_generator).symm⟩
    have hg0 : g ≠ 0 := by rintro rfl; exact hPne (by rw [hg, Ideal.span_singleton_eq_bot])
    haveI : NeZero g.natAbs := ⟨Int.natAbs_ne_zero.2 hg0⟩
    rw [hg]
    exact Finite.of_equiv _ (Int.quotientSpanEquivZMod g).toEquiv.symm
  exact Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient ℤ P R 𝔪 Ideal.map_comap_le

end S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int
end P2MW
export P2MW.S_Algebra_FiniteType_exists_isMaximal_and_finite_quotient_of_int (solution)
