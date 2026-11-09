-- Prove2me | Definitions.Def_ProxGapTight_Lm
-- name    : ProxGapTight_Lm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:54.625445+00:00
-- url     : https://prove2.me/theorems/48f2bbf7-6d7f-4a4f-82bb-050ba8e96919
-- title:
--   Cutoff weight $L_m=3Q^{m-3}-3Q^{m-4}-1$
-- statement:
--   For integers $Q\ge2$ and $m\ge4$,
--   $$
--   L_m=3Q^{m-3}-3Q^{m-4}-1,
--   $$
--   the cutoff weight below which words of $U_m$ are combinations of at most two incidence vectors.
--
--   **Formalization Note** Natural-number arithmetic; no subtraction truncates for $Q\ge2$, $m\ge4$, the range in which the paper uses $L_m$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), Lemma 3.2, p.7, display

import Mathlib

namespace ProxGapTight

/-- The cutoff weight `L_m := 3Q^{m−3} − 3Q^{m−4} − 1`, Kominers, Thaler, Zheng, manuscript
(Sept. 2026), Lemma 3.2, p.7, display.

**Formalization Note.** Natural-number arithmetic; for `Q ≥ 2` and `m ≥ 4` no subtraction
truncates (`3Q^{m−4}(Q − 1) ≥ 3`), which is the only range in which the paper uses `L_m`
(statements using it are for all sufficiently large `m`). -/
def Lm (Q m : ℕ) : ℕ := 3 * Q ^ (m - 3) - 3 * Q ^ (m - 4) - 1

end ProxGapTight


