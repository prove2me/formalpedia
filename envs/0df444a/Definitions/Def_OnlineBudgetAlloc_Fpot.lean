-- Prove2me | Definitions.Def_OnlineBudgetAlloc_Fpot
-- name    : OnlineBudgetAlloc_Fpot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:40.693342+00:00
-- url     : https://prove2.me/theorems/f3771a77-0fa3-4169-bc69-4e2e2de9ce58
-- title:
--   The function $F(s) = \tfrac34(1 - H/s)_+ + \tfrac14(1 - \tfrac23 H/s)_+$
-- statement:
--   For a parameter $H$ (in the paper $H = N/e$) and $s > 0$, display (6) defines
--   $$
--   F(s) = \frac34\Bigl(1 - \frac{H}{s}\Bigr)_+ + \frac14\Bigl(1 - \frac23\cdot\frac{H}{s}\Bigr)_+, \qquad z_+ = \max\{z, 0\}.
--   $$
--   By Lemma 6, $F(s_t)$ bounds the change of the potential on a final-phase item when $s_t$ advertisers remain. It appears in displays (5), (7), (9) and in Lemmas 7 and 8.
--
--   **Formalization Note** At $s = 0$, Lean's convention $H/0 = 0$ gives $F(0) = 1$. This is a single point and does not affect any integral of $F$.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6, eq. (6)

import Mathlib

namespace OnlineBudgetAlloc

/-- The function `F(s) = (3/4)(1 − H/s)₊ + (1/4)(1 − (2/3)·H/s)₊` of display (6)
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6), with `z₊ = max(z, 0)`; `H` is a parameter (in the paper `H = N/e`).

**Formalization Note** At `x = 0` Lean's `H / 0 = 0` gives `F(0) = 1`; this single point does not
affect any integral of `F`. -/
noncomputable def Fpot (H x : ℝ) : ℝ :=
  3 / 4 * max (1 - H / x) 0 + 1 / 4 * max (1 - 2 / 3 * (H / x)) 0

end OnlineBudgetAlloc


