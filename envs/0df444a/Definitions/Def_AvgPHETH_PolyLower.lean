-- Prove2me | Definitions.Def_AvgPHETH_PolyLower
-- name    : AvgPHETH_PolyLower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:33.002997+00:00
-- url     : https://prove2.me/theorems/a86265dc-9404-4e3e-a1c1-311b9fcb7e0a
-- title:
--   $w\ge n^{\Omega(1)}$
-- statement:
--   There is $a>0$ with $n^a\le w(n)$ for all sufficiently large $n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (i), p.3 (PDF 5)

import Mathlib

namespace AvgPHETH

/-- `w ≥ n^{Ω(1)}` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (i), p.3 (PDF 5)): there is `a > 0` with `n^a ≤ w(n)` for
sufficiently large `n`. -/
def PolyLower (w : ℕ → ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) ^ a ≤ (w n : ℝ)

end AvgPHETH


