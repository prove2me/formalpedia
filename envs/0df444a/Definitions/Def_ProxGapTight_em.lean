-- Prove2me | Definitions.Def_ProxGapTight_em
-- name    : ProxGapTight_em
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:49.984028+00:00
-- url     : https://prove2.me/theorems/b772635a-e70b-4206-83d1-aedc32ac1665
-- title:
--   $e_m=(Q^{m-2}-1)/(Q-1)$
-- statement:
--   For integers $Q\ge2$ and $m\ge2$,
--   $$
--   e_m=\frac{Q^{m-2}-1}{Q-1},
--   $$
--   the number of lines in a codimension-two subspace of $\mathbb F_Q^m$, i.e. the weight of an incidence vector and the minimum distance of $U_m$.
--
--   **Formalization Note** Natural-number arithmetic, exact for $Q\ge2$, $m\ge2$; the paper uses $e_m$ only for large $m$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.2, p.7, display

import Mathlib

namespace ProxGapTight

/-- `e_m := (Q^{m−2} − 1)/(Q − 1)`, the number of lines in a codimension-two subspace of `F_Q^m`,
Kominers, Thaler, Zheng, manuscript (Sept. 2026), Lemma 3.2, p.7, display.

**Formalization Note.** Natural-number arithmetic; exact for `Q ≥ 2` and `m ≥ 2`, the only range
in which the paper uses it (every statement using `em` is for `m` large or `m ≥ 4`). -/
def em (Q m : ℕ) : ℕ := (Q ^ (m - 2) - 1) / (Q - 1)

end ProxGapTight


