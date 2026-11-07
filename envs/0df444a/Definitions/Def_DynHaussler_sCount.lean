-- Prove2me | Definitions.Def_DynHaussler_sCount
-- name    : DynHaussler_sCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:39.460398+00:00
-- url     : https://prove2.me/theorems/55bd11fc-98bc-4acf-95d3-795985cce162
-- title:
--   Completion-rule count $S_r(n)=\sum_{i=0}^{\min\{r,n\}}\binom ni$
-- statement:
--   For integers $r,n\ge0$,
--   $$
--   S_r(n)=\sum_{i=0}^{\min\{r,n\}}\binom{n}{i},
--   $$
--   the number of subsets of $[n]$ of size at most $r$. It bounds the number of partial SOA completion rules (Lemma 16) and enters the adaptive sampling bound (Lemma 17).
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 16, p.22 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The count `S_r(n) = ∑_{i=0}^{min{r,n}} binom(n, i)` of partial SOA completion rules.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Lemma 16, p.22 (PDF p.24). -/
def sCount (r n : ℕ) : ℕ := ∑ i ∈ Finset.range (min r n + 1), Nat.choose n i

end DynHaussler


