-- Prove2me | Definitions.Def_EffRobustLearn_signPM
-- name    : EffRobustLearn_signPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:39.617301+00:00
-- url     : https://prove2.me/theorems/25cfb2b5-6b96-423d-a6e1-c777586fb781
-- title:
--   The sign function with $\mathrm{sign}(0)=+1$
-- statement:
--   The sign function used in (2.2), (2.3) and (A.10) is $\mathrm{sign}(z)=+1$ for $z\ge0$ and $\mathrm{sign}(z)=-1$ for $z<0$.
--
--   The paper does not fix $\mathrm{sign}(0)$. Since $\mathrm{Maj}_k(C)\subseteq\{\pm1\}^X$ must be a Boolean class, the value lies in $\{\pm1\}$, and this development takes $+1$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eqs. (2.2), (2.3), p.11 (PDF p.12)

import Mathlib

namespace EffRobustLearn

/-- The sign function of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), (2.2), (2.3), p.11, and (A.10), p.32, with values in `{±1}`:
`sign z = +1` for `z ≥ 0` and `-1` for `z < 0`.

**Formalization Note.** The paper does not fix `sign 0`. Since `Maj_k(C) ⊆ {±1}^X` (2.3), and its VC dimension
is taken in Fact C.3 item 5, the value must lie in `{±1}`; this development reads `sign 0 = +1`. Inequality (A.10) holds under
this convention. -/
noncomputable def signPM (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

end EffRobustLearn


