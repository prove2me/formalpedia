-- Prove2me | Definitions.Def_MersenneLPW_mersenneExponentCount
-- name    : MersenneLPW_mersenneExponentCount
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T15:24:53.540869+00:00
-- url     : https://prove2.me/theorems/1f0d37aa-a426-4924-a5e4-a9ed5c15191f
-- title:
--   Mersenne prime exponent counting function $C(y)$
-- statement:
--   For a natural number $y$, the **Mersenne prime exponent counting function** is
--   $$C(y) = \#\{\, p \in \mathbb{N} : p < y,\ 2^p - 1 \text{ is prime} \,\}.$$
--   It counts exponents, not the Mersenne primes themselves, and the bound is strict ($p < y$). This is the counting function appearing in the Lenstra–Pomerance–Wagstaff conjecture, which predicts $C(y) \sim e^{\gamma}\log_2 y$ as $y \to \infty$, where $\gamma$ is the Euler–Mascheroni constant.
--
--   **Formalization Note.** The definition is `Nat.count (fun p => (mersenne p).Prime) y`, where `mersenne p = 2 ^ p - 1` is Mathlib's Mersenne number and `Nat.count` counts the naturals strictly below `y` satisfying a decidable predicate; decidability of primality is Mathlib's `Nat.decidablePrime` instance. The strict bound follows the FormalConjectures library; replacing $p < y$ by $p \le y$ changes $C$ by at most one and does not affect the conjectured asymptotic.
-- source:
--   FormalConjectures (Google DeepMind), PR #7866, FormalConjectures/Wikipedia/Mersenne.lean, definition mersenneExponentCount, https://github.com/google-deepmind/formal-conjectures/pull/7866 ; S. S. Wagstaff Jr., Divisors of Mersenne numbers, Math. Comp. 40 (161) (1983), 385-397, doi:10.1090/S0025-5718-1983-0679454-X ; https://en.wikipedia.org/wiki/Mersenne_conjectures#Lenstra%E2%80%93Pomerance%E2%80%93Wagstaff_conjecture

import Mathlib

namespace MersenneLPW

/-- `mersenneExponentCount y` counts the exponents `p < y` such that `2 ^ p - 1` is a
Mersenne prime. -/
def mersenneExponentCount (y : ℕ) : ℕ := Nat.count (fun p => (mersenne p).Prime) y

end MersenneLPW


