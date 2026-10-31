-- Prove2me | Definitions.Def_StaticProphetSec_UT
-- name    : StaticProphetSec_UT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:07.068337+00:00
-- url     : https://prove2.me/theorems/7ba62460-88a3-43b9-b43b-ed8dd9303dcc
-- title:
--   Utilization $\mathrm{UT}_k(d)=\min(1,d/k)$
-- statement:
--   For $k\ge1$ and $d\in\mathbb N_0$,
--
--   $$\mathrm{UT}_k(d)=\min\left(1,\frac dk\right).$$
--
--   When realized demand is $d$, this is the fraction of the $k$ items that are allocated. It measures the risk of under-allocation.
--
--   **Formalization Note** The function is defined for every natural $k$; each statement using it assumes $k\ge1$, so the value at $k=0$ never enters.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (4), p.15

import Mathlib

namespace StaticProphetSec

/-- The utilization function `UT_k(d) = min(1, d/k)`, equation (4) (Arnosti & Ma,
arXiv:2108.12893v2, (4), p.15): when realized demand is `d`, the fraction of the `k` items that
are allocated.

**Formalization Note.** `k` is a natural number and every statement using `UT` assumes `1 ≤ k`
(the paper's `ℕ` is the positive integers, p.15), so the junk value `d / 0 = 0` is never used. -/
noncomputable def UT (k d : ℕ) : ℝ :=
  min 1 ((d : ℝ) / (k : ℝ))

end StaticProphetSec


