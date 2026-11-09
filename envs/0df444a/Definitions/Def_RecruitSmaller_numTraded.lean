-- Prove2me | Definitions.Def_RecruitSmaller_numTraded
-- name    : RecruitSmaller_numTraded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:25.742926+00:00
-- url     : https://prove2.me/theorems/37dc9b0c-1526-421a-91e7-77d3925fab8b
-- title:
--   Number of pairs traded by Seller Trade Reduction $t(b,s_k)$
-- statement:
--   For $b\in\mathbb R^m$ and $s_k\in\mathbb R^k$ let $r'=r(b,s_k)$ be the efficient trade size. **Seller Trade Reduction** trades
--   $$
--   t(b,s_k) := \begin{cases} 0, & r'=0,\\[2pt] r' - \mathbb 1\bigl[b^{(r')} < s^{(r'+1)}_k\bigr], & r'\ge1,\end{cases}
--   $$
--   pairs, with the sentinel $s^{(k+1)}_k=+\infty$. In the unreduced case $b^{(r')}\ge s^{(r'+1)}_k$ the top $r'$ pairs trade at price $s^{(r'+1)}_k$; otherwise the top $r'-1$ pairs trade, buyers paying $b^{(r')}$ and sellers receiving $s^{(r')}_k$.
--
--   **Formalization Note** The comparison with the sentinel is made in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`); prices are not modelled since they do not enter the Gains From Trade.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4, p.11

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrdExt
import Definitions.Def_RecruitSmaller_tradeSize

namespace RecruitSmaller

/-- The **number of traded pairs of Seller Trade Reduction** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Definition 2.4,
p.11): with `r′ := r(b, sₖ)`, `t(b, sₖ) := 0` if `r′ = 0`, and
`t(b, sₖ) := r′ − 𝟙[b⁽ʳ′⁾ < s⁽ʳ′⁺¹⁾ₖ]` if `r′ ≥ 1`, using the sentinel `s⁽ᵏ⁺¹⁾ₖ = +∞`.

**Formalization Note** The comparison is in `WithTop ℝ` (`sellerOrdExt`), so `r′ = k` always
reduces, as on the page. -/
noncomputable def numTraded {m k : ℕ} (b : Fin m → ℝ) (s : Fin k → ℝ) : ℕ :=
  if tradeSize b s = 0 then 0
  else tradeSize b s -
    (if ((buyerOrd b (tradeSize b s) : ℝ) : WithTop ℝ) < sellerOrdExt s (tradeSize b s + 1)
      then 1 else 0)

end RecruitSmaller


