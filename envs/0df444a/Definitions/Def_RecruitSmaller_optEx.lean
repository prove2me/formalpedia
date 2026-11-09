-- Prove2me | Definitions.Def_RecruitSmaller_optEx
-- name    : RecruitSmaller_optEx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:15.215468+00:00
-- url     : https://prove2.me/theorems/7da236d1-a633-4646-be2a-af600e87fa96
-- title:
--   Ex-post first-best Gains From Trade $\mathrm{OPT}(b,s_n)$
-- statement:
--   For a buyer profile $b\in\mathbb R^m$ and a seller profile $s_n\in\mathbb R^n$, the **ex-post first-best Gains From Trade** is
--   $$
--   \mathrm{OPT}(b,s_n) := \sum_{i=1}^{r(b,s_n)} \bigl(b^{(i)}-s^{(i)}_n\bigr),
--   $$
--   where $r(b,s_n)$ is the efficient trade size. Every summand is nonnegative.
--
--   When $m\ge n\ge1$ the page also writes it as $\sum_{i=1}^{n}(b^{(i)}-s^{(i)}_n)^+$; that equality is a consequence and is not built in.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_tradeSize

namespace RecruitSmaller

/-- The **ex-post first-best Gains From Trade** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.3, p.11):
`OPT(b, sₙ) := ∑_{i=1}^{r(b, sₙ)} (b⁽ⁱ⁾ − s⁽ⁱ⁾ₙ)` with `r` the efficient trade size.

**Formalization Note** This is the page's defining form (the sum up to `r`); the page's second form
`∑_{i=1}^n (b⁽ⁱ⁾ − s⁽ⁱ⁾ₙ)⁺` for `m ≥ n ≥ 1` is a consequence, not built in. Every summand is
nonnegative (`b⁽ⁱ⁾ ≥ b⁽ʳ⁾ ≥ s⁽ʳ⁾ₙ ≥ s⁽ⁱ⁾ₙ` for `i ≤ r`). -/
noncomputable def optEx {m n : ℕ} (b : Fin m → ℝ) (s : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (tradeSize b s), (buyerOrd b i - sellerOrd s i)

end RecruitSmaller


