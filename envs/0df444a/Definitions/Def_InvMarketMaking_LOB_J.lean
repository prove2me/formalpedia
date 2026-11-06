-- Prove2me | Definitions.Def_InvMarketMaking_LOB_J
-- name    : InvMarketMaking_LOB_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:42.925057+00:00
-- url     : https://prove2.me/theorems/79b48705-8212-4efa-ae82-ccf0f3ae086b
-- title:
--   Seller c.d.f. $F$, buyer survival function $S$, surrogate objective $J(b,a)=(a-b)\min\{F(b),S(a)\}$ and its optimum $J^*$
-- statement:
--   Let $\mathcal V$ be the joint law of a round's valuations $(V^{\mathrm{sell}},V^{\mathrm{buy}})$. Define the **seller c.d.f.** and the **buyer survival function**
--   $$
--   F(b)=\mathbb P(V^{\mathrm{sell}}\le b),\qquad S(a)=\mathbb P(V^{\mathrm{buy}}\ge a),
--   $$
--   so that $F(b)$ is the probability that a seller accepts the bid $b$ and $S(a)$ the probability that a buyer accepts the ask $a$. The **surrogate objective** and its **optimal value** are
--   $$
--   J(b,a)=(a-b)\min\{F(b),S(a)\},\qquad J^*=\sup_{(b,a)\in[0,1]^2}J(b,a).
--   $$
--   $J(b,a)$ is the spread earned on the matched volume $\min\{F(b),S(a)\}$ of a bid–ask pair; $J^*$ is the benchmark of the surrogate regret.
--
--   **Formalization Note** The supremum ranges over all of $[0,1]^2$, including pairs with $b\ge a$ (where $J\le 0$), as in the paper. For a probability law every value of $J$ on $[0,1]^2$ lies in $[-1,1]$, so the real supremum is the genuine one. $S$ uses the non-strict inequality $V^{\mathrm{buy}}\ge a$: the paper writes $S(a)=\mathbb E[\mathbb I(V^{\mathrm{buy}}\ge a)]=1-F_{\mathrm{buy}}(a)$, and the two expressions differ only at atoms; the expectation of the trade indicator is the definition used.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Sec. 3.3, p. 16 (F, S) and Definition 3.2, Eq. (4), p. 17 (J, J*)

import Mathlib

namespace InvMarketMaking.LOB

open MeasureTheory

/-- The seller c.d.f. `F(b) = P(V^sell ≤ b)` of the valuation law `V` (Maran, Restelli, Stradi,
arXiv:2610.24562v1, Sec. 3.3, p. 16: `E[I(V^sell_t ≤ b)] = F_sell(b) =: F(b)`).

**Formalization Note** The first coordinate of `V` is the seller's valuation. -/
noncomputable def sellCdf (V : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  (V {p | p.1 ≤ b}).toReal

/-- The buyer survival function `S(a) = P(V^buy ≥ a)` of the valuation law `V` (arXiv:2610.24562v1,
Sec. 3.3, p. 16: `E[I(V^buy_t ≥ a)] =: S(a)`; also p. 59, `S(a) = P(−V^buy_t ≤ −a)`).

**Formalization Note** The inequality is `≥` (non-strict), the probability that a buyer with
valuation `V^buy` accepts the ask `a`. Page 16 also writes this as `1 − F_buy(a)`, which differs
from `P(V^buy ≥ a)` exactly at atoms of `V^buy`; the expectation `E[I(V^buy ≥ a)]`, which is what the
trade indicator and every later use need, is taken as the definition. -/
noncomputable def buySurv (V : Measure (ℝ × ℝ)) (a : ℝ) : ℝ :=
  (V {p | a ≤ p.2}).toReal

/-- The surrogate objective `J(b, a) = (a − b) · min{F(b), S(a)}` (arXiv:2610.24562v1,
Definition 3.2, Eq. (4), p. 17). -/
noncomputable def J (V : Measure (ℝ × ℝ)) (b a : ℝ) : ℝ :=
  (a - b) * min (sellCdf V b) (buySurv V a)

/-- The optimal surrogate value `J* = sup_{b,a ∈ [0,1]²} (a − b) min{F(b), S(a)}`
(arXiv:2610.24562v1, Definition 3.2, p. 17).

**Formalization Note** The supremum ranges over all of `[0,1]²`, including pairs with `b ≥ a`, as
on the page. For a probability measure `V` every value lies in `[−1, 1]`, so the real `⨆` is the
genuine supremum (not Lean's junk value for unbounded families). -/
noncomputable def Jstar (V : Measure (ℝ × ℝ)) : ℝ :=
  ⨆ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, J V p.1 p.2

end InvMarketMaking.LOB


