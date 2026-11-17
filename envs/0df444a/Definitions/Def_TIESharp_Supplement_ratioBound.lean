-- Prove2me | Definitions.Def_TIESharp_Supplement_ratioBound
-- name    : TIESharp_Supplement_ratioBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:54:04.653182+00:00
-- url     : https://prove2.me/theorems/6a597867-d928-4798-95e9-14bfaf9072fb
-- title:
--   The ratio of Theorem 1.3: $(n+1)/2$ for $n\ge7$; $3$, $105/32$, $29/8$ for $n=4,5,6$
-- statement:
--   For a number of machines $n$, let
--
--   $$R(n)=\begin{cases}\dfrac{n+1}{2}, & n\ge 7,\\[4pt] \dfrac{29}{8}, & n=6,\\[4pt] \dfrac{105}{32}, & n=5,\\[4pt] 3, & n=4.\end{cases}$$
--
--   These are the upper bounds on the optimal truthful-in-expectation approximation ratio $\rho(n)$ given by Theorem 1.1 ($n\ge7$) and Theorem 1.2 ($n=4,5,6$); Theorem 1.3 asserts that one efficiently implementable mechanism attains all of them. At $n=7$ the value is $4=(7+1)/2$, not the cruder $4+1/32$ of the basic makespan estimate.
--
--   **Formalization Note** The four cases are written out. For $n\le3$ the definition returns $3$; that value is never used, since every statement about $R(n)$ assumes $n\ge4$.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorems 1.1–1.3, p.2 (PDF p.3)

import Mathlib

set_option autoImplicit false

namespace TIESharp

namespace Supplement

/-- The **approximation ratio of Theorem 1.3** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Theorems 1.1–1.3, p.2): "the upper bounds of Theorems 1.1 and 1.2
for every n ≥ 4", that is `(n + 1)/2` for `n ≥ 7` (Theorem 1.1), `3` for `n = 4`, `105/32` for
`n = 5` and `29/8` for `n = 6` (Theorem 1.2).

**Formalization Note.** The four cases are written out explicitly. For `n ≤ 3` the value is `3`;
it is never used: every statement about `ratioBound n` assumes `4 ≤ n`. -/
noncomputable def ratioBound (n : ℕ) : ℝ :=
  if 7 ≤ n then ((n : ℝ) + 1) / 2
  else if n = 6 then 29 / 8
  else if n = 5 then 105 / 32
  else 3

end Supplement

end TIESharp


