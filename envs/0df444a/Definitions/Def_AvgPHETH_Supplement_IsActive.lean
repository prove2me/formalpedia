-- Prove2me | Definitions.Def_AvgPHETH_Supplement_IsActive
-- name    : AvgPHETH_Supplement_IsActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:33:04.835659+00:00
-- url     : https://prove2.me/theorems/c67f289b-fe59-43ec-a439-7e13c5a41139
-- title:
--   Active pairs $(k,n)$
-- statement:
--   A pair $(k,n)$ of natural numbers is **active** if
--
--   $$k\ge1,\qquad n\ge16,\qquad R(n)^k\le\sqrt n,$$
--
--   where $R(n)=g(n)\log n$. The oracle $V_k$ stores a selector tree for the input $x$ exactly when $(k,|x|)$ is active; for every fixed $k$ all sufficiently large $n$ are active.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_RPar

namespace AvgPHETH.Supplement

/-- The pair `(k, n)` is **active**: `k ≥ 1`, `n ≥ 16` and `R(n)^k ≤ √n`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41)). -/
def IsActive (ε : ℕ → ℝ) (k n : ℕ) : Prop := 1 ≤ k ∧ 16 ≤ n ∧ RPar ε n ^ k ≤ Real.sqrt n

end AvgPHETH.Supplement


