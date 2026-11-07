-- Prove2me | Definitions.Def_SoftmaxAttnFD_F
-- name    : SoftmaxAttnFD_F
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:32.168817+00:00
-- url     : https://prove2.me/theorems/7de82b96-0f5d-4bd5-a39d-02932b1083e1
-- title:
--   The running-time function $F_d(m,n)$ and the potential $\Phi(m,n)$
-- statement:
--   For a natural number $k$ and reals $m,n$, the potential is $\Phi(m,n)=(mn)^{k/(k+1)}$. With $k(d)=\lfloor d/2\rfloor$,
--   $$F_d(m,n)=(mn)^{k(d)/(k(d)+1)}+m+n\qquad(m,n\ge1).$$
--   This is the running-time function of the paper: every batch bound has the form $\tilde O(F_d(m,n))$. At $d=1$ the exponent is $0$, so $F_1(m,n)=1+m+n$; at $d=2,3$ it is within a factor $2$ of $m+n$.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), (2.1), p.11; §7.5, p.33

import Mathlib

namespace SoftmaxAttnFD

/-- The potential `Φ(m, n) = (mn)^{k/(k+1)}` (arXiv:2611.06055, sha256 a60f7609…, §7.5, p.33). -/
noncomputable def Phi (k : ℕ) (m n : ℝ) : ℝ :=
  (m * n) ^ ((k : ℝ) / ((k : ℝ) + 1))

/-- `F_d(m, n) = (mn)^{k(d)/(k(d)+1)} + m + n` with `k(d) = ⌊d/2⌋` (arXiv:2611.06055, (2.1), p.11).

**Formalization Note** `d / 2` is natural-number division, which is the floor; the exponent is taken
in `ℝ`. At `d = 1` the exponent is `0`, so `F_1(m, n) = 1 + m + n`. The page defines `F_d` for
`m, n ≥ 1`, and every statement using it has those hypotheses. -/
noncomputable def F (d m n : ℕ) : ℝ :=
  Phi (d / 2) (m : ℝ) (n : ℝ) + (m : ℝ) + (n : ℝ)

end SoftmaxAttnFD


