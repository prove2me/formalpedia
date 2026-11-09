-- Prove2me | Definitions.Def_RecruitSmaller_betaDens
-- name    : RecruitSmaller_betaDens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:08:56.810444+00:00
-- url     : https://prove2.me/theorems/629b9508-eed5-47d5-905b-452cd4a63160
-- title:
--   Beta$(i,n-i+1)$ density $f_{i,n}(w)$
-- statement:
--   For integers $n\ge i\ge1$,
--   $$
--   f_{i,n}(w) := n\binom{n-1}{i-1}w^{i-1}(1-w)^{n-i},\qquad w\in(0,1),
--   $$
--   the density of the Beta$(i,n-i+1)$ distribution, i.e. of the $i$-th smallest of $n$ i.i.d. Uniform$(0,1)$ variables.
--
--   **Formalization Note** The polynomial is defined on all of $\mathbb R$; statements integrate it over subintervals of $[0,1]$ or restrict it to $(0,1)$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.6, p.13 and Lemma 3.8, p.15

import Mathlib

namespace RecruitSmaller

/-- The **Beta(i, n − i + 1) density** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.6, p.13; Lemma 3.8, p.15):
`f_{i,n}(w) := n · C(n−1, i−1) · w^{i−1} (1 − w)^{n−i}` on `(0, 1)`.

**Formalization Note** The polynomial is defined on all of `ℝ`; every statement integrates it over a
subinterval of `[0, 1]` or restricts it to `(0, 1)`. Ranks satisfy `1 ≤ i ≤ n` in every use, where
the natural-number exponents are the true ones. -/
noncomputable def betaDens (n i : ℕ) (w : ℝ) : ℝ :=
  (n : ℝ) * ((n - 1).choose (i - 1) : ℝ) * w ^ (i - 1) * (1 - w) ^ (n - i)

end RecruitSmaller


