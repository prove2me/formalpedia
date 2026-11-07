-- Prove2me | Definitions.Def_DynHaussler_nCount
-- name    : DynHaussler_nCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:38.057609+00:00
-- url     : https://prove2.me/theorems/97e5dfaf-d8c4-4251-919b-50d51ae40572
-- title:
--   Schedule count $n_i(m)=2^i\binom{m+i-1}{i}$
-- statement:
--   For integers $i,m\ge0$,
--   $$
--   n_i(m)=2^i\binom{m+i-1}{i},\qquad n_0(m)=1 .
--   $$
--   It is the number of correction schedules of depth $i$ with ordinals in $[m]$: there are $\binom{m+i-1}{i}$ weakly increasing ordinal lists of length $i$ in $[m]$, each with $2^i$ sign assignments.
--
--   **Formalization Note** Natural-number arithmetic; at $i=0$ the truncated $m+0-1$ gives $\binom{m-1}{0}=1$ for every $m$, which is the paper's $n_0(m)=1$.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (35), p.20 (PDF p.22)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The number `n_i(m) = 2^i · binom(m + i − 1, i)` of correction schedules of depth `i` with
ordinals in `[m]` (weakly increasing ordinal lists of length `i` in `[m]`, each with one of `2^i`
sign assignments), with `n_0(m) = 1`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (35), p.20 (PDF p.22).

**Formalization Note** Natural-number arithmetic: at `i = 0` the truncated `m + 0 − 1` gives
`binom(m − 1, 0) = 1` for every `m`, which is the paper's `n_0(m) = 1`. -/
def nCount (i m : ℕ) : ℕ := 2 ^ i * Nat.choose (m + i - 1) i

end DynHaussler


