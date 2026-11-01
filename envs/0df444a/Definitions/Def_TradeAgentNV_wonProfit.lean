-- Prove2me | Definitions.Def_TradeAgentNV_wonProfit
-- name    : TradeAgentNV_wonProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:36.34527+00:00
-- url     : https://prove2.me/theorems/7ce08ca2-7fd0-40eb-b072-382db446a371
-- title:
--   Realized profit after a won bid
-- statement:
--   If the bid $b$ wins, the agent pays $bq$ for the seller's $q$ units, of which a fraction $u\in[0,1]$ (the yield) is usable, and ships $\min(qu,D)$ units to meet the buyer's demand $D$. It earns $r-t$ per unit shipped (revenue minus shipping cost), pays the excess-supply cost $h$ per unit of excess supply $(qu-D)^+$ and the lost-sales cost $\pi$ per unit of unmet demand $(D-qu)^+$. The realized profit is
--   $$
--   (r-t)\min(qu,D)-bq-h\,(qu-D)^+-\pi\,(D-qu)^+ .
--   $$
--
--   **Formalization Note** Display (3) as printed attaches $h$ to $(D-qU)^+$ and $\pi$ to $(qU-D)^+$. That contradicts the definitions of $h$ and $\pi$ on p.8, and only the assignment used here yields display (4); this definition follows p.8 and (4).
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, §3.2, pp.8–10, first line of display (3) (with the costs as defined on p.8), optimal shipping quantity $x^*=\min(Q^y,D)$ on p.9

import Mathlib

namespace TradeAgentNV

/-- The trade agent's **realized profit when the bid is won** (the first line of display (3),
p.10, and §3, pp.8–9, of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)), when the realized yield fraction is `u`:
the agent receives `qu` units, ships `min(qu, D)` (the optimal shipping quantity
`x* = min(Qʸ, D)`, p.9), earns `r − t` per unit shipped, pays `bq` to the seller, pays the
excess-supply cost `h` per unit of excess supply `(qu − D)⁺` and the lost-sales cost `π` per
unit of unmet demand `(D − qu)⁺`:
`(r − t)·min(qu, D) − bq − h·(qu − D)⁺ − π·(D − qu)⁺`.

**Formalization Note.** Display (3) as printed attaches `h` to `(D − qU)⁺` and `π` to
`(qU − D)⁺`. That contradicts the definitions of `h` (cost per unit of supply in excess of
demand) and `π` (cost per unit of demand unmet) on p.8, and only the assignment used here gives
display (4). This definition follows p.8 and display (4). `(x)⁺` is `max x 0`. -/
noncomputable def wonProfit (r t h π D q b u : ℝ) : ℝ :=
  (r - t) * min (q * u) D - b * q - h * max (q * u - D) 0 - π * max (D - q * u) 0

end TradeAgentNV


