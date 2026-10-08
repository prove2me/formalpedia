-- Prove2me | Definitions.Def_Helfgott_PrimePowerRemoval
-- name    : Helfgott_PrimePowerRemoval
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-04T20:59:47.456804+00:00
-- url     : https://prove2.me/theorems/d9bf3229-bd2d-4678-80f8-3e51bbce1541
-- title:
--   Odd-prime triples and von Mangoldt weighted terms
-- statement:
--   Define the odd-prime predicate, the triples summing to N with at least one coordinate not an odd prime, and the signed von Mangoldt term Λ(i)Λ(j)Λ(k)a(i)a(j)b(k). These data support the removal of higher prime powers and the even prime from a weighted ternary representation count. No nonnegativity of the smoothing weights is imposed.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (7.3), (7.19), (7.49)–(7.50), https://arxiv.org/abs/1312.7748 . Elementary replacement for the prime-power removal estimates in the concluding argument. Written by Codex.

import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped BigOperators

namespace Helfgott

def IsOddPrime (n : ℕ) : Prop := Nat.Prime n ∧ Odd n

noncomputable def badTripleIndices (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (tripleIndices N).filter
    (fun t => ¬ (IsOddPrime t.1.1 ∧ IsOddPrime t.1.2 ∧ IsOddPrime t.2))

noncomputable def weightedTripleTerm (a b : ℕ → ℝ) (t : (ℕ × ℕ) × ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt t.1.1 : ℝ) *
    (ArithmeticFunction.vonMangoldt t.1.2 : ℝ) *
    (ArithmeticFunction.vonMangoldt t.2 : ℝ) * (a t.1.1 * a t.1.2 * b t.2)

end Helfgott


