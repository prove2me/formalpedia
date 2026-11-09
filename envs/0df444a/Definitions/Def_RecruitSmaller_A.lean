-- Prove2me | Definitions.Def_RecruitSmaller_A
-- name    : RecruitSmaller_A
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:08:56.694715+00:00
-- url     : https://prove2.me/theorems/10d68df5-dd43-41a1-b570-81c6663ce9d4
-- title:
--   Recruitment-gain coefficient $A_{n,i}(p)$
-- statement:
--   For integers $n\ge i\ge1$ and $p\in[0,1]$,
--   $$
--   A_{n,i}(p) := \binom{n}{i-1}(1-p)^{n-i+1}(2-p)+\binom{n}{i-2}(1-p)^{n-i+2},
--   $$
--   with the convention $\binom{n}{-1}:=0$.
--
--   The quantity $p^iA_{n,i}(p)$ is the gain in $\Pr[s^{(i)}\le x]$ from recruiting two extra sellers (Lemma 3.5).
--
--   **Formalization Note** The convention is explicit: the second term is present only for $i\ge2$. The definition accepts any $n,i,p$; every statement uses $1\le i\le n$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), eq. (3.3), p.12

import Mathlib

namespace RecruitSmaller

/-- The **recruitment-gain coefficient** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), eq. (3.3), p.12):
`A_{n,i}(p) := C(n, i−1)(1 − p)^{n−i+1}(2 − p) + C(n, i−2)(1 − p)^{n−i+2}`, with the convention
`C(n, −1) := 0`.

**Formalization Note** The convention is explicit: the second term is present only for `i ≥ 2`
(in `ℕ`, `i − 2 = 0` at `i = 1` and `C(n, 0) = 1`, which would be wrong). Exponents are natural
numbers; the page uses `1 ≤ i ≤ n`, where `n − i + 1` and `n − i + 2` are the true values. -/
noncomputable def A (n i : ℕ) (p : ℝ) : ℝ :=
  (n.choose (i - 1) : ℝ) * (1 - p) ^ (n - i + 1) * (2 - p) +
    (if 2 ≤ i then (n.choose (i - 2) : ℝ) else 0) * (1 - p) ^ (n - i + 2)

end RecruitSmaller


