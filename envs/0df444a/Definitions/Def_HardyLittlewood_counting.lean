-- Prove2me | Definitions.Def_HardyLittlewood_counting
-- name    : HardyLittlewood_counting
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T21:31:15.06938+00:00
-- url     : https://prove2.me/theorems/c946fa5a-267e-4631-a5fe-470d5f31cb0b
-- title:
--   Counting functions: constellations and primes below a bound
-- statement:
--   The counting layer of the Hardy–Littlewood conjectures. For a tuple of offsets m, the counting function π_P(n) returns the number of admissible prime constellations (p, p + 2m₁, ..., p + 2m_k) whose base point p is at most n. The prime-counting function π(n) returns the number of primes at most n. The second Hardy–Littlewood conjecture for a pair (x, y) is the subadditivity claim π(x + y) ≤ π(x) + π(y). Both counting functions are defined as the cardinalities of the corresponding finite sets of natural numbers.
-- source:
--   Formal Conjectures (2025), HardyLittlewood.lean, definitions Nat.primeTupleCounting and SecondHardyLittlewoodConjectureFor; the counting functions of Hardy and Littlewood (1923), Acta Math. 44

import Mathlib
import Definitions.Def_HardyLittlewood_constellation

namespace HardyLittlewood

/-- π_P(n): the number of admissible prime constellations
(p, p + 2·m₁, ..., p + 2·m_k) whose base point p is at most n. -/
noncomputable def primeTupleCounting {k : ℕ} (m : Fin k.succ → ℕ) (n : ℕ) : ℕ :=
  {p : ℕ | p ≤ n ∧ IsAdmissiblePrimeConstellation m p}.ncard

/-- π(n): the prime-counting function — the number of primes at most n. -/
noncomputable def primeCounting (n : ℕ) : ℕ :=
  {p : ℕ | p ≤ n ∧ p.Prime}.ncard

/-- The second Hardy–Littlewood conjecture for the pair (x, y):
π(x + y) ≤ π(x) + π(y). -/
def secondHardyLittlewoodFor (x y : ℕ) : Prop :=
  primeCounting (x + y) ≤ primeCounting x + primeCounting y

end HardyLittlewood


