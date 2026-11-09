-- Prove2me | Definitions.Def_ProxGapTight_nm
-- name    : ProxGapTight_nm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:50.240209+00:00
-- url     : https://prove2.me/theorems/80c589f3-ec7b-479e-b287-c51402ecb9af
-- title:
--   $n_m=(Q^m-1)/(Q-1)$
-- statement:
--   For integers $Q\ge2$ and $m$,
--   $$
--   n_m=\frac{Q^m-1}{Q-1},
--   $$
--   the number of lines of $\mathbb F_Q^m$, i.e. the length of the code $U_m$.
--
--   **Formalization Note** Natural-number division, which is exact for $Q\ge2$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.2, p.7, display

import Mathlib

namespace ProxGapTight

/-- `n_m := (Q^m − 1)/(Q − 1)`, the number of lines of `F_Q^m`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), Lemma 3.2, p.7, display.

**Formalization Note.** Natural-number division; it is exact for `Q ≥ 2` (`Q − 1` divides
`Q^m − 1`). -/
def nm (Q m : ℕ) : ℕ := (Q ^ m - 1) / (Q - 1)

end ProxGapTight


