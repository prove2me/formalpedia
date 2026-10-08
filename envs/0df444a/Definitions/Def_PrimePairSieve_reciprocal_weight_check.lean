-- Prove2me | Definitions.Def_PrimePairSieve_reciprocal_weight_check
-- name    : PrimePairSieve_reciprocal_weight_check
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T16:31:19.368372+00:00
-- url     : https://prove2.me/theorems/2615fd30-bad2-4c77-ae6c-46a33fae3e12
-- title:
--   Kernel-checkable prime factor certificate
-- statement:
--   Boolean test that a finite set of primes multiplies to a given $n$; used to certify squarefree indices in sparse reciprocal-sieve tables.

import Mathlib
import Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight
open scoped BigOperators
set_option autoImplicit false
namespace PrimePairSieve
def reciprocal_weight_check (n : ℕ) (s : Finset ℕ) : Bool :=
  decide ((∀ p ∈ s, Nat.Prime p) ∧ (∏ p ∈ s, p) = n)
end PrimePairSieve


