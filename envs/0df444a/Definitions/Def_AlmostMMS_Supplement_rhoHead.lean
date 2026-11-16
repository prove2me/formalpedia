-- Prove2me | Definitions.Def_AlmostMMS_Supplement_rhoHead
-- name    : AlmostMMS_Supplement_rhoHead
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:33.201783+00:00
-- url     : https://prove2.me/theorems/c7cbe2a8-60ae-4f69-ba21-6db124d5035f
-- title:
--   The head-rounding loss $\rho(h,X)=8+4\log X\,(1+\ln h+\ln X)$
-- statement:
--   For a head size $h\ge1$ and a number $X$ of strictly fractional entries, the head-rounding loss is
--   $$
--   \rho(h,X)=8+4\log_2 X\cdot\bigl(1+\ln h+\ln X\bigr),
--   $$
--   with $\log$ the binary and $\ln$ the natural logarithm. It bounds how many selected agents are lost when fractional head profiles are rounded to integral ones (Theorem 2.2).
--
--   **Formalization Note** At $X=0$ both logarithms evaluate to $0$ in Lean, so $\rho(h,0)=8$; in that case the fractional profiles are already integral and nothing is lost.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 2.2, p.18

import Mathlib

namespace AlmostMMS.Supplement

/-- **The head-rounding loss** `ρ(h, X) = 8 + 4 log X · (1 + ln h + ln X)` (Theorem 2.2, p.18).
Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** `log` is base `2` (`Real.logb 2`; p.50 bounds the number of phases `K ≤ log X`
from `X_k ≤ 4 + (X - 4) 2^{-(k-1)}`, and p.19 rewrites `4 log(nd) · 2 ln(nd)` as `8 ln 2 log²(nd)`),
and `ln` is `Real.log`. At `X = 0` both logarithms are `0` in Lean, so `ρ(h, 0) = 8`; there the
fractional profile is already integral. -/
noncomputable def rhoHead (h X : ℕ) : ℝ :=
  8 + 4 * Real.logb 2 (X : ℝ) * (1 + Real.log (h : ℝ) + Real.log (X : ℝ))

end AlmostMMS.Supplement


