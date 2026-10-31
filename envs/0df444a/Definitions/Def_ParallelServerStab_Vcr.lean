-- Prove2me | Definitions.Def_ParallelServerStab_Vcr
-- name    : ParallelServerStab_Vcr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:16.902259+00:00
-- url     : https://prove2.me/theorems/6ac4e2fa-d3a7-4cac-8cd8-5839c9cf0064
-- title:
--   The allocation vector $p_{p,2}$ and the critical value $V_{cr}(p)$ of (9)
-- statement:
--   Consider $s \ge 2$ identical servers. Servers are ranked by queue length after every event, rank $1$ being the shortest queue. The **allocation vector** of the policy J2SQ$(p)$, for an error probability $p\in[0,1]$, is
--
--   $$
--   \mathbf p_{p,2} = (1-p,\ p,\ 0,\ \dots,\ 0):
--   $$
--
--   a job routed by this vector joins the shortest queue with probability $1-p$ and the second-shortest queue with probability $p$. The case $p=1$ is $\mathbf p_{1,2}=(0,1,0,\dots,0)$, join-the-second-shortest-queue (J2SQ).
--
--   For $p>0$ the **critical value** is
--
--   $$
--   V_{cr}(p) = \frac{s-1}{2s}\left(1+\sqrt{1+\frac{4}{p(s-1)}}\right).
--   $$
--
--   These two objects are the parameters of Theorem 2: the non-idling J2SQ$(p)$ system can be stable only below $V_{cr}(p)\wedge 1$.
--
--   **Formalization Note** Ranks are 0-based (`pp2 s p 0 = 1 - p`, `pp2 s p 1 = p`). `Vcr s p` is the real number of (9) whenever $p>0$ and $s\ge2$; at $p=0$ Lean's division by zero gives the value $(s-1)/s$, which is not the paper's (the paper's convention is $V_{cr}(0)=+\infty$), so every statement of this mission uses `Vcr s p` only under $0<p$.
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5, p.10 (p_{p,2}); §5.1, p.11 (p_{1,2}); eq. (9), p.11

import Mathlib

namespace ParallelServerStab

/-- The allocation vector `p_{p,2} = (1 − p, p, 0, …, 0)` of the policy J2SQ(p)
(Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5, p. 10): an
arrival that finds every server busy joins the shortest queue with probability `1 − p` and the
second-shortest queue with probability `p`.

**Formalization Note.** Ranks are 0-based: `pp2 s p i` is the probability of rank `i`, where
rank `0` is the shortest queue (the paper's index 1) and rank `1` the second-shortest (the
paper's index 2). For `0 ≤ p ≤ 1` and `s ≥ 2` it is a probability vector, an element of the
paper's `Π_s` (p. 7). -/
def pp2 (s : ℕ) (p : ℝ) : Fin s → ℝ :=
  fun i => if i.val = 0 then 1 - p else if i.val = 1 then p else 0

/-- The allocation vector `p_{1,2} = (0, 1, 0, …, 0)` of join-the-second-shortest-queue, J2SQ
(Moyal–Perry, arXiv:1904.10331v1, §5.1, p. 11); it is `p_{p,2}` at `p = 1`. -/
def p12 (s : ℕ) : Fin s → ℝ := pp2 s 1

/-- The critical value of (9) (Moyal–Perry, Stability of Parallel Server Systems,
arXiv:1904.10331v1, eq. (9), p. 11): for `s` servers and an error probability `p > 0`,
`V_cr(p) = (s − 1)/(2s) · (1 + √(1 + 4/(p(s − 1))))`.

**Formalization Note.** The paper defines `V_cr(p)` for `p > 0` only. Lean's division and
square root are total: at `p = 0` (or `s = 1`) the term `4/(p(s − 1))` is `0` and `Vcr s 0` is
`(s − 1)/s`, which is **not** the paper's value (the paper's convention `V_cr(0) = +∞` is the
limit `p → 0⁺`). Every statement of this mission uses `Vcr s p` only under `0 < p` and
`2 ≤ s`, where `1 + 4/(p(s − 1)) > 1` and the formula is exactly (9). The paper also writes
`V_cr(p, 2)` and `V_cr(p, s)` (pp. 12, 14, 15) for the same number. -/
noncomputable def Vcr (s : ℕ) (p : ℝ) : ℝ :=
  ((s : ℝ) - 1) / (2 * (s : ℝ)) * (1 + Real.sqrt (1 + 4 / (p * ((s : ℝ) - 1))))

end ParallelServerStab


