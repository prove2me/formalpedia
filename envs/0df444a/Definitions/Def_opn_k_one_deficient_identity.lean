-- Prove2me | Definitions.Def_opn_k_one_deficient_identity
-- name    : opn_k_one_deficient_identity
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-12T16:24:41.552964+00:00
-- url     : https://prove2.me/theorems/8a0cfa30-e039-4e94-bc32-30d9cdc3f063
-- title:
--   The k=1 Dris equations give the deficient-perfect identity
-- statement:
--   Under the canonical k=1 quotient equations m^2=((p+1)/2)d and sigma(m^2)=p d, with p congruent to 1 modulo 4, the square m^2 satisfies 2m^2=sigma(m^2)+d. Thus d is its deficient divisor.
-- source:
--   Elementary algebraic consequence of the canonical k=1 Dris quotient equations; no external classification theorem is used.

import Mathlib

namespace OddPerfectNumber

theorem k_one_deficient_identity (p m d : Nat)
    (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) :
    2 * m ^ 2 = (∑ x ∈ (m ^ 2).divisors, x) + d := by
  have hhalf : 2 * ((p + 1) / 2) = p + 1 := by
    omega
  calc
    2 * m ^ 2 = 2 * (((p + 1) / 2) * d) := by rw [hdvd]
    _ = (2 * ((p + 1) / 2)) * d := by ring
    _ = (p + 1) * d := by rw [hhalf]
    _ = p * d + d := by ring
    _ = (∑ x ∈ (m ^ 2).divisors, x) + d := by rw [← hsig]

end OddPerfectNumber


