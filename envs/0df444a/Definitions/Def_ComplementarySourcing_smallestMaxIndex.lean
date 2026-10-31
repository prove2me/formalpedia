-- Prove2me | Definitions.Def_ComplementarySourcing_smallestMaxIndex
-- name    : ComplementarySourcing_smallestMaxIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:32.400992+00:00
-- url     : https://prove2.me/theorems/8f37cd3f-1ec2-4438-85e3-5e7b6da96bd6
-- title:
--   The index $k$
-- statement:
--   The smallest index $k\in\{1,2\}$ with $\pi_k=\max\{\pi_1,\pi_2\}$: index $1$ when $\pi_2\le\pi_1$, and index $2$ otherwise.
--
--   **Formalization Note** The index set is `Fin 2`, so the paper's indices $1,2$ are `0`, `1`.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.13, Proposition 2

import Mathlib

namespace ComplementarySourcing

/-- The paper's `k`: the smallest index in `{1, 2}` with `π_k = max{π₁, π₂}`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Proposition 2, p.13 (PDF 13).

**Formalization Note.** The index set is `Fin 2`, so the paper's index `1` is `0` and its `2` is
`1`. -/
noncomputable def smallestMaxIndex (π₁ π₂ : ℝ) : Fin 2 :=
  if π₂ ≤ π₁ then 0 else 1

end ComplementarySourcing


