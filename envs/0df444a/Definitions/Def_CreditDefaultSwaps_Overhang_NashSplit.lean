-- Prove2me | Definitions.Def_CreditDefaultSwaps_Overhang_NashSplit
-- name    : CreditDefaultSwaps_Overhang_NashSplit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:02:15.531826+00:00
-- url     : https://prove2.me/theorems/2dcf507e-11fd-49cb-9ea8-256317928e83
-- title:
--   Weighted transferable-utility Nash split with endpoint weights
-- statement:
--   For a joint value $T$, disagreement payoffs $d_1,d_2$, and a weight $w\in[0,1]$, the individually rational transferable-utility Nash split is the pair
--   $$v_1=d_1+w(T-d_1-d_2),\qquad v_2=d_2+(1-w)(T-d_1-d_2),\qquad T\ge d_1+d_2.$$
--   This general allocation rule is defined separately from the financial model. It gives the whole surplus to the second party at $w=0$ and to the first at $w=1$. The paper applies it with the equity disagreement payoff zero, creditor disagreement payoff $R$, and total available value $V_n+\mathcal C$.
--
--   Differences from the source:
--   - encoding: a Nash product and its displayed split → the explicit surplus-sharing relation including individual rationality and endpoint weights; reason: this expresses equations (5)–(6) without an ambiguous zero-power convention.
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, §3.1.2, equations (5)–(6), printed pp. 10–11 (PDF pp. 11–12)

import Mathlib

namespace CreditDefaultSwaps.Overhang

/-- Weighted transferable-utility Nash allocation, including endpoint weights.
The two disagreement payoffs are `d₁,d₂`; `total` is the available joint value. -/
def NashSplit (weight total d₁ d₂ v₁ v₂ : ℝ) : Prop :=
  0 ≤ weight ∧ weight ≤ 1 ∧ d₁ + d₂ ≤ total ∧
  v₁ = d₁ + weight * (total - d₁ - d₂) ∧
  v₂ = d₂ + (1 - weight) * (total - d₁ - d₂)

end CreditDefaultSwaps.Overhang


