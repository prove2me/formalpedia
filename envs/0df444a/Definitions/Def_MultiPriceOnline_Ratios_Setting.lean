-- Prove2me | Definitions.Def_MultiPriceOnline_Ratios_Setting
-- name    : MultiPriceOnline_Ratios_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:40.13837+00:00
-- url     : https://prove2.me/theorems/f59b162e-924e-46fa-93c3-63187680cd0b
-- title:
--   §2.1, pp. 13–14 — price sets, the booking limits (7) and (8) of Proposition 1, and F(𝒫), G(𝒫) (Definition 2)
-- statement:
--   A **price set** $\mathcal P$ consists of $m$ prices $r^{(1)}, \dots, r^{(m)}$ with
--   $$0 < r^{(1)} < r^{(2)} < \dots < r^{(m)},$$
--   and the convention $r^{(0)} := 0$.
--
--   The **booking limits** of $\mathcal P$ are positive numbers $\alpha^{(1)}, \dots, \alpha^{(m)}$ with $\alpha^{(1)} + \dots + \alpha^{(m)} = 1$ such that, for every $j = 2, \dots, m$,
--   $$1 - e^{-\alpha^{(1)}} = \frac{1}{1 - r^{(j-1)}/r^{(j)}}\,\bigl(1 - e^{-\alpha^{(j)}}\bigr). \qquad (7)$$
--   The **Ball–Queyranne booking limits** are positive numbers $\sigma^{(1)}, \dots, \sigma^{(m)}$ with $\sigma^{(1)} + \dots + \sigma^{(m)} = 1$ such that, for every $j = 2, \dots, m$,
--   $$\sigma^{(1)} = \frac{1}{1 - r^{(j-1)}/r^{(j)}}\,\sigma^{(j)}. \qquad (8)$$
--   Proposition 1 of the paper shows that each system has exactly one solution. From them, Definition 2 sets
--   $$F(\mathcal P) = 1 - e^{-\alpha^{(1)}}, \qquad G(\mathcal P) = \sigma^{(1)}.$$
--   $F(\mathcal P)$ is the paper's tight competitive ratio for many items sharing the price set $\mathcal P$; $\sigma^{(1)}$ is the tight ratio of Ball and Queyranne (2009) for a single item.
--
--   **Formalization Note** Prices are a sequence $r : \mathbb N \to \mathbb R$ read at the indices $1, \dots, m$; `price r j` is $r^{(j)}$ with $r^{(0)} = 0$. The booking limits are not constructed: `IsBookingLimits m r α` and `IsBQLimits m r σ` are predicates stating (7) resp. (8) together with positivity and the sum condition on the indices $1, \dots, m$. Theorems take $\alpha$, $\sigma$ as variables satisfying these predicates; by Proposition 1 (a theorem of this mission) such variables are exactly the paper's booking limits on $1, \dots, m$. The denominators $1 - r^{(j-1)}/r^{(j)}$ are positive under the price-set hypothesis. `F α` and `G σ` read $F(\mathcal P)$ and $G(\mathcal P)$ off these variables.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, pp. 11, 13–14, §2 (r⁽⁰⁾ := 0), Proposition 1 (7)–(8), Definition 2

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Ranking_Setting

namespace MultiPriceOnline.Ratios

open Finset

/-- Definition 2: `G(𝒫) = σ⁽¹⁾`, read off the Ball–Queyranne limits `σ`. -/
def G (σ : ℕ → ℝ) : ℝ := σ 1

end MultiPriceOnline.Ratios


