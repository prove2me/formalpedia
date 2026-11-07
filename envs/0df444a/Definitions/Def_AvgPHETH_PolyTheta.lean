-- Prove2me | Definitions.Def_AvgPHETH_PolyTheta
-- name    : AvgPHETH_PolyTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:49.615419+00:00
-- url     : https://prove2.me/theorems/9604872c-677e-46f2-a163-c6b49ac0366a
-- title:
--   $m(n)=n^{\Theta(1)}$
-- statement:
--   There are $a,b,A>0$ with $n^a/A\le m(n)\le A\,n^b$ for all sufficiently large $n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.1, p.19 (PDF 21)

import Mathlib

namespace AvgPHETH

/-- `m(n) = n^{Θ(1)}` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.1, p.19 (PDF 21)): there are `a, b, A > 0` with
`n^a / A ≤ m(n) ≤ A n^b` for sufficiently large `n`. -/
def PolyTheta (m : ℕ → ℕ) : Prop :=
  ∃ a b A : ℝ, 0 < a ∧ 0 < b ∧ 0 < A ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (n : ℝ) ^ a / A ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ A * (n : ℝ) ^ b

end AvgPHETH


