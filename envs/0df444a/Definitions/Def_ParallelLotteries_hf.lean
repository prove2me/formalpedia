-- Prove2me | Definitions.Def_ParallelLotteries_hf
-- name    : ParallelLotteries_hf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:09.306006+00:00
-- url     : https://prove2.me/theorems/0909f288-0376-46f4-8403-cbe36ccfb8d8
-- title:
--   The functions $h(p)=\frac{pk}{1-(1-p)^k}$ and $f(p_i,p_j)$ of (59)–(60)
-- statement:
--   For an integer $k\ge1$ define (60)
--   $$h(p):=\frac{pk}{1-(1-p)^k}\quad(0<p\le1),\qquad h(0):=1,$$
--   and (59)
--   $$f(p_i,p_j):=\frac{p_j-1/k}{p_j-p_i}\,h(p_i)+\frac{1/k-p_i}{p_j-p_i}\,h(p_j),$$
--   used on the region $0\le p_i<1/k<p_j\le1$.
--
--   $f(p_i,p_j)$ is the largest welfare ratio a trade can achieve for an agent whose best affordable bundle mixes items with win probabilities $p_i<1/k<p_j$; it is the constant $\gamma$ of the two-item case in the proof of Theorem 2. Its supremum $2-1/k$ is the constant of Theorem 2.
--
--   **Formalization Note** (60) is $0/0$ at $p=0$, but Lemma 7 evaluates $h$ at $p_i=0$; $h(0)$ is set to $1$, the limit of $h(p)$ as $p\to0^+$. In Lean, $f$ is defined for all real arguments, but every statement about it restricts to the region above.
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (59) and (60), p.34

import Mathlib

namespace ParallelLotteries

/-- **The function `h`**, display (60), Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2, p.34:
`h(p) := p k / (1 − (1 − p)^k)`.

**Formalization Note.** (60) is `0/0` at `p = 0`, while Lemma 7 (p.34) evaluates `h` at `p_i = 0`.
`h(0)` is set to `1`, the limit of `p k / (1 − (1 − p)^k)` as `p → 0⁺`. For `0 < p ≤ 1` and
`k ≥ 1` the denominator is positive. -/
noncomputable def hfun (k : ℕ) (p : ℝ) : ℝ :=
  if p = 0 then 1 else p * k / (1 - (1 - p) ^ k)

/-- **The function `f`**, display (59), Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2, p.34:
`f(p_i, p_j) := (p_j − 1/k)/(p_j − p_i) · h(p_i) + (1/k − p_i)/(p_j − p_i) · h(p_j)`,
used on the region `0 ≤ p_i < 1/k < p_j ≤ 1`, where `p_j − p_i > 0`. -/
noncomputable def fval (k : ℕ) (pi pj : ℝ) : ℝ :=
  (pj - 1 / (k : ℝ)) / (pj - pi) * hfun k pi + (1 / (k : ℝ) - pi) / (pj - pi) * hfun k pj

end ParallelLotteries


