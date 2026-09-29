-- Prove2me | Definitions.Def_opn_k_one_incoming_sigma_source_v2
-- name    : opn_k_one_incoming_sigma_source_v2
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-12T16:32:02.490024+00:00
-- url     : https://prove2.me/theorems/7cca391f-a124-42bc-9c3f-e7c010b17683
-- title:
--   A q divisor of the Dris cofactor has a distinct incoming sigma source
-- statement:
--   If p and q are distinct primes, q divides the Dris cofactor d, and sigma(m^2)=p d, then some prime factor r of m^2 distinct from q has q dividing its local divisor sum. The proof uses the published source-extraction lemma, the factorization of a square, and the local sum being 1 modulo its own base.
-- source:
--   Elementary composition of the published Prove2Me lemmas exists_p_source_of_dvd, sq_factorization_two, and local_sum_mod_self. This is only the predecessor-edge step; it does not claim chain termination or contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_exists_p_source_of_dvd
import Theorems.Thm_OddPerfectNumber_sq_factorization_two
import Theorems.Thm_OddPerfectNumber_local_sum_mod_self

namespace OddPerfectNumber

theorem k_one_incoming_sigma_source_v2 (p q m d : Nat)
    (hp : p.Prime)
    (hq : q.Prime)
    (hqp : q ≠ p)
    (hm2 : m ^ 2 ≠ 0)
    (hqd : q ∣ d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) :
    ∃ r ∈ (m ^ 2).primeFactors,
      r ≠ q ∧
        q ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i := by
  have hqSigma : q ∣ (∑ x ∈ (m ^ 2).divisors, x) := by
    rw [hsig]
    obtain ⟨c, hc⟩ := hqd
    refine ⟨p * c, ?_⟩
    rw [hc]
    ring
  have hqpow : q ^ 1 ∣ (∑ x ∈ (m ^ 2).divisors, x) := by
    simpa using hqSigma
  obtain ⟨r, hrmem, hrlocal⟩ :=
    exists_p_source_of_dvd q 1 m hq (by omega) hm2 hqpow
  refine ⟨r, hrmem, ?_, hrlocal⟩
  intro hrq
  subst r
  have hfac := sq_factorization_two (m := m) (q := q)
  rw [hfac] at hrlocal
  have hzero := Nat.dvd_iff_mod_eq_zero.mp hrlocal
  have hone := local_sum_mod_self q (m.factorization q) hq
  omega

end OddPerfectNumber


