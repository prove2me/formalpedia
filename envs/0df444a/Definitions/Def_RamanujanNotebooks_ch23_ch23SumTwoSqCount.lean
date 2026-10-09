-- Prove2me | Definitions.Def_RamanujanNotebooks_ch23_ch23SumTwoSqCount
-- name    : RamanujanNotebooks_ch23_ch23SumTwoSqCount
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T23:02:25.85146+00:00
-- url     : https://prove2.me/theorems/b0aec94f-135a-4f64-806a-b48f0e7f3066
-- title:
--   Ramanujan's Notebooks, Part IV, Ch. 23: ch23SumTwoSqCount
-- statement:
--   `ch23SumTwoSqCount x` is Landau's `B(x)` (Chapter 23, Entry 13, pp. 60-62): the number of
--   positive integers `n ≤ x` that are a sum of two squares of integers (`0` allowed as a
--   square, so `1, 2, 4, 5, 8, 9, 10, …` are counted).
--   Total: for every real `x` the set is finite (empty for `x < 1`), so `Nat.card` is its true
--   cardinality and no junk value occurs.
--   Reference: `B(10) = 7`, `B(100) = 43`, `B(1000) = 330`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 23.

import Mathlib

namespace RamanujanNotebooks

/-- `ch23SumTwoSqCount x` is Landau's `B(x)` (Chapter 23, Entry 13, pp. 60-62): the number of
positive integers `n ≤ x` that are a sum of two squares of integers (`0` allowed as a
square, so `1, 2, 4, 5, 8, 9, 10, …` are counted).
Total: for every real `x` the set is finite (empty for `x < 1`), so `Nat.card` is its true
cardinality and no junk value occurs.
Reference: `B(10) = 7`, `B(100) = 43`, `B(1000) = 330`. -/
noncomputable def ch23SumTwoSqCount (x : ℝ) : ℕ :=
  Nat.card {n : ℕ // 0 < n ∧ (n : ℝ) ≤ x ∧ ∃ a b : ℕ, n = a ^ 2 + b ^ 2}

end RamanujanNotebooks


