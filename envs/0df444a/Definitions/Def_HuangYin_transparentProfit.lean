-- Prove2me | Definitions.Def_HuangYin_transparentProfit
-- name    : HuangYin_transparentProfit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:50.518009+00:00
-- url     : https://prove2.me/theorems/676d98e4-1e2f-442f-96f7-cc7e19464d8d
-- title:
--   Two-period profit under transparent selling
-- statement:
--   Under transparent selling the firm sells product $m_t\in\{H,L\}$ openly at price $p_t$ in period $t=1,2$. Every customer values product $m$ at $v_m$, so the whole unit mass of customers buys iff $p_t\le v_{m_t}$, and each sale earns $p_t-c_{m_t}$. The two-period profit is
--
--   $$\sum_{t=1}^{2}\mathbf 1\{p_t\le v_{m_t}\}\,(p_t-c_{m_t}).$$
--
--   The paper's benchmark policies (selling $H$ at $v_H$, or $L$ at $v_L$, in both periods) are special cases.
--
--   **Formalization Note** The firm may choose a product and a price separately in each period. Offering both products at once adds nothing, since all customers are identical. A customer buys at zero net utility, as in rule (1).
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3.3 Benchmark, p. 11

import Mathlib
import Definitions.Def_HuangYin_Product_value
import Definitions.Def_HuangYin_Product_unitCost

namespace HuangYin

/-- **The firm's two-period profit under transparent selling** (§3.3, p. 11; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §3.3 "Benchmark", p. 11: "The firm uses a transparent selling policy for product H with
a retailing price pH and product L with a retailing price pL. Each customer would obtain a net
utility vH − pH from buying product H and would obtain a net utility vL − pL from buying
product L."

In period `t` the firm sells product `mt` openly at price `pt`. Every customer values it at
`mt.value`, so the whole unit mass buys iff `pt ≤ mt.value` (net utility nonnegative), and each
sale earns `pt − mt.unitCost`.

**Formalization Note.** The firm chooses a product and a price in each period separately; this
contains the paper's policies (one product, `pH = vH` or `pL = vL`, in both periods). Offering
both products at once adds nothing, since all customers are identical and buy the same one. A
customer buys at zero net utility, as in rule (1). -/
noncomputable def transparentProfit (P : Params) (m1 m2 : Product) (p1 p2 : ℝ) : ℝ :=
  (if p1 ≤ m1.value P then 1 else 0) * (p1 - m1.unitCost P) +
    (if p2 ≤ m2.value P then 1 else 0) * (p2 - m2.unitCost P)

end HuangYin


