-- Prove2me | Definitions.Def_RecruitSmaller_psi
-- name    : RecruitSmaller_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:43.837329+00:00
-- url     : https://prove2.me/theorems/a79b16a2-7a1d-4955-9eee-4f6af9294422
-- title:
--   Truncated integrand $\psi_{n,i}(w;p)$
-- statement:
--   For integers $n\ge i\ge1$ and $p\in[0,1]$, the **truncated integrand** on $[0,1]$ is
--   $$
--   \psi_{n,i}(w;p) := A_{n,i}(p)-\binom{n+2}{i}\min(1-p,w)^{n+2-i}.
--   $$
--   It is non-increasing in $w$, and its integral against a Beta density controls $I_i(x)$ from below (Lemmas 3.7–3.9).
--
--   **Formalization Note** Defined for all real $w,p$; statements take $p\in[0,1]$ and integrate over $w\in[0,r]\subseteq[0,1]$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.7, eq. (3.10), p.14

import Mathlib
import Definitions.Def_RecruitSmaller_A

namespace RecruitSmaller

/-- The **truncated integrand** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.7, eq. (3.10), p.14):
`ψ_{n,i}(w; p) := A_{n,i}(p) − C(n+2, i) · min(1 − p, w)^{n+2−i}`.

**Formalization Note** Defined for all real `w` and `p`; the page takes `w ∈ [0, 1]`, `p ∈ [0, 1]`,
and every statement integrates over `w ∈ [0, r] ⊆ [0, 1]` with `p ∈ [0, 1]`. -/
noncomputable def psi (n i : ℕ) (p w : ℝ) : ℝ :=
  A n i p - ((n + 2).choose i : ℝ) * (min (1 - p) w) ^ (n + 2 - i)

end RecruitSmaller


