-- Prove2me | Definitions.Def_MatchVec3_minEntropy
-- name    : MatchVec3_minEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:52.940213+00:00
-- url     : https://prove2.me/theorems/26bb7009-a31d-479d-8581-57976185b4c5
-- title:
--   Min-entropy $H_\infty$
-- statement:
--   The **min-entropy** of a random variable $X$ is
--
--   $$H_\infty(X)=-\log\max_x\mathbb P[X=x].$$
--
--   **Formalization Note** $\log$ is the natural logarithm: the paper fixes no base and pairs $\log$ with $\exp$ in Theorem 1.2. The maximum is a supremum in $[0,\infty]$, which is at most $1$ and has no junk value, and it is attained for finitely supported laws.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §2.1, p.8

import Mathlib

namespace MatchVec3

/-- **Min-entropy** `H∞(X) = − log max_x P[X = x]` (Aggarwal, Obremski, STOC 2027 submission
(manuscript sha256 44199413…), §2.1, p.8).

**Formalization Note** `log` is the natural logarithm: the paper fixes no base and pairs `log` with
`exp` in Theorem 1.2. The maximum is a supremum in `ℝ≥0∞`, which is at most `1` and has no junk value;
for a finitely supported law it is attained. -/
noncomputable def minEntropy {α : Type*} (X : PMF α) : ℝ :=
  -Real.log (⨆ x, X x).toReal

end MatchVec3


