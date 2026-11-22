-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
-- name    : Formalism_PeriodIntegrals_PrimesDyadicRS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:39.34211+00:00
-- url     : https://prove2.me/theorems/2311c0dc-a679-4609-acb8-86b39af4c7bc
-- title:
--   Primes Dyadic RS
-- statement:
--   Definitions and structural lemmas for Primes Dyadic RS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PrimesDyadicRS.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PrimesDyadicRS
def Claim : Prop :=
  ∀ y : ℝ, 41 / 2 ≤ y →
    3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)
end PI.PrimesDyadicRS


