-- Prove2me | Definitions.Def_CrossLicensing_Innovation_Model
-- name    : CrossLicensing_Innovation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:29.952771+00:00
-- url     : https://prove2.me/theorems/b4a4f4e1-7264-4d11-b4fb-451b42e0b0f1
-- title:
--   §3, (1)–(2) — the cross-licensing supply chain: Cournot quantities, the supplier's least optimal price, gross profits and the innovation game
-- statement:
--   The model of §3. A monopolistic supplier sells a key component at wholesale price $r$ to two manufacturers $M_1, M_2$. Manufacturer $M_i$ improves its quality by $T_i \ge 0$; with **cross-licensing of effectiveness** $\beta$, its quality improvement is $Q_i = T_i + \beta T_j$ ($j \ne i$), and its inverse demand is $p_i = 1 + Q_i - q_i - q_j$ (market size normalized to $1$, unit production cost $0$).
--
--   1. **Standing assumptions** (p. 9): $0 \le \beta \le 1$ and $49/144 < k_2 < k_1$, where $k_i$ is $M_i$'s innovation cost coefficient ($M_2$ is the superior manufacturer).
--   2. **Quantity game** (1): given $(T_1, T_2)$ and $r$, $M_i$ chooses $q_i \ge 0$ to maximize
--   $$\Pi_i(q_i; q_j) = (1 + T_i + \beta T_j - q_i - q_j - r)\,q_i.$$
--   3. **Cournot quantities** (2), in symmetric form. Write $a = 1 + T_1 + \beta T_2$, $b = 1 + T_2 + \beta T_1$. If $r \le 2\min(a,b) - \max(a,b)$ the outcome is the duopoly $q_1 = (2a - b - r)/3$, $q_2 = (2b - a - r)/3$; else if $r \le \max(a,b)$ only the manufacturer with the larger intercept sells (manufacturer 2 on ties), the quantity $(\max(a,b) - r)/2$; otherwise $q_1 = q_2 = 0$. For $T_2 \ge T_1$ this is the paper's display (2), with $r_1 = 1 + T_1(2-\beta) - T_2(1-2\beta)$ and $r_2 = 1 + T_1\beta + T_2$.
--   4. **Supplier.** Its profit is $\pi_s(r) = r(q_1 + q_2)$ at the Cournot quantities. The supplier's price $r^*(T_1, T_2)$ is the **least** maximizer of $\pi_s$ over $r \ge 0$.
--   5. **Gross profits** $\Pi^*_i(T_1, T_2 \mid \beta)$: $M_i$'s profit (1) at $r = r^*(T_1,T_2)$ and the Cournot quantities at that price.
--   6. **Innovation game**: $M_i$ chooses $T_i \ge 0$ and earns $\Pi^*_i(T_1, T_2 \mid \beta) - k_i T_i^2$; its pure Nash equilibria (no manufacturer gains by a unilateral deviation to another $T_i \ge 0$) are the paper's innovation equilibria. The quantity game's equilibria are defined in the same way over $q_i \ge 0$.
--   7. **Duopoly** at $(T_1, T_2)$: both manufacturers sell a positive quantity at $r^*(T_1, T_2)$.
--
--   **Formalization Note** The paper prints (2) only for $T_2 \ge T_1$ ("without loss of generality"); in the innovation game $M_1$ may deviate above $T_2$, so the quantities are defined for every profile, with whichever manufacturer has the larger intercept as the possible monopolist. The supplier's price is defined as the least maximizer, never by Lemma 1's case rule; the least-price tie-break resolves the supplier's indifference at $T_2 = \hat T_2(T_1 \mid \beta)$ toward the duopoly, as Lemma 1 does. Wholesale prices range over $[0, \infty)$, an assumption the paper leaves implicit. Both games use the published two-player pure Nash equilibrium predicate `CompetingChains.Cournot.IsPureNash`, with strategy type $\mathbb R_{\ge 0}$ (`NNReal`) for quantities and innovation levels.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), pp. 8–10, §3, displays (1)–(2); p. 12, Lemma 1

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

namespace CrossLicensing.Innovation

/-- Standing assumptions (p. 9): cross-licensing effectiveness `0 ≤ β ≤ 1`, and innovation cost
coefficients `49/144 < k2 < k1` (manufacturer 2 is the superior one). -/
def Standing (β k1 k2 : ℝ) : Prop :=
  0 ≤ β ∧ β ≤ 1 ∧ 49 / 144 < k2 ∧ k2 < k1

/-- Demand intercept of manufacturer 1, `A + Q1` with `A = 1` and `Q1 = T1 + β T2`. -/
def qual1 (β T1 T2 : ℝ) : ℝ := 1 + T1 + β * T2

/-- Demand intercept of manufacturer 2, `A + Q2` with `A = 1` and `Q2 = T2 + β T1`. -/
def qual2 (β T1 T2 : ℝ) : ℝ := 1 + T2 + β * T1

/-- Manufacturer 1's profit (1): `(1 + T1 + β T2 − q1 − q2 − r) q1`. -/
def mfrProfit1 (β T1 T2 r q1 q2 : ℝ) : ℝ := (1 + T1 + β * T2 - q1 - q2 - r) * q1

/-- Manufacturer 2's profit (1): `(1 + T2 + β T1 − q2 − q1 − r) q2`. -/
def mfrProfit2 (β T1 T2 r q1 q2 : ℝ) : ℝ := (1 + T2 + β * T1 - q2 - q1 - r) * q2

/-- Manufacturer 1's payoff in the quantity (Cournot) game (1) at innovation levels `(T1, T2)` and
wholesale price `r`, on nonnegative quantities. -/
def quantityPayoff1 (β T1 T2 r : ℝ) (q1 q2 : NNReal) : ℝ := mfrProfit1 β T1 T2 r q1 q2

/-- Manufacturer 2's payoff in the quantity game (1), on nonnegative quantities. -/
def quantityPayoff2 (β T1 T2 r : ℝ) (q1 q2 : NNReal) : ℝ := mfrProfit2 β T1 T2 r q1 q2

/-- `(q1, q2)` is a pure Nash equilibrium of the quantity game (1): each manufacturer's quantity is a
best response over all nonnegative quantities. -/
def IsQuantityEquilibrium (β T1 T2 r : ℝ) (q1 q2 : NNReal) : Prop :=
  CompetingChains.Cournot.IsPureNash (quantityPayoff1 β T1 T2 r) (quantityPayoff2 β T1 T2 r) q1 q2

/-- The Cournot quantities (2), in symmetric form: with `a = qual1`, `b = qual2`, the firm with the
larger intercept is the possible monopolist (firm 2 on ties). Duopoly
`((2a − b − r)/3, (2b − a − r)/3)` if `r ≤ 2 min(a, b) − max(a, b)`; monopoly of the larger firm
with quantity `(max(a, b) − r)/2` if `r ≤ max(a, b)`; `(0, 0)` otherwise. For `T2 ≥ T1` and
`β ≤ 1` this is the printed (2), with `r1 = 2a − b` and `r2 = b`. -/
noncomputable def quantities (β T1 T2 r : ℝ) : ℝ × ℝ :=
  let a := qual1 β T1 T2
  let b := qual2 β T1 T2
  if r ≤ 2 * min a b - max a b then ((2 * a - b - r) / 3, (2 * b - a - r) / 3)
  else if r ≤ max a b then
    (if a ≤ b then (0, (b - r) / 2) else ((a - r) / 2, 0))
  else (0, 0)

/-- The supplier's profit `r (q1 + q2)` at the Cournot quantities. -/
noncomputable def supplierProfit (β T1 T2 r : ℝ) : ℝ :=
  r * ((quantities β T1 T2 r).1 + (quantities β T1 T2 r).2)

/-- The supplier's optimal wholesale prices: the maximizers of `supplierProfit` over `r ≥ 0`. -/
def optimalPrices (β T1 T2 : ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ ∀ r', 0 ≤ r' → supplierProfit β T1 T2 r' ≤ supplierProfit β T1 T2 r}

/-- The supplier's wholesale price `r*(T1, T2)`: the least optimal price (ties are broken toward the
lower price, i.e. toward the duopoly). -/
noncomputable def price (β T1 T2 : ℝ) : ℝ := sInf (optimalPrices β T1 T2)

/-- Manufacturer 1's gross profit `Π*_1(T1, T2 | β)`: its profit (1) at the supplier's price and the
Cournot quantities at that price. -/
noncomputable def grossProfit1 (β T1 T2 : ℝ) : ℝ :=
  mfrProfit1 β T1 T2 (price β T1 T2)
    (quantities β T1 T2 (price β T1 T2)).1 (quantities β T1 T2 (price β T1 T2)).2

/-- Manufacturer 2's gross profit `Π*_2(T1, T2 | β)`. -/
noncomputable def grossProfit2 (β T1 T2 : ℝ) : ℝ :=
  mfrProfit2 β T1 T2 (price β T1 T2)
    (quantities β T1 T2 (price β T1 T2)).1 (quantities β T1 T2 (price β T1 T2)).2

/-- Manufacturer 1's payoff in the innovation game, `Π*_1(T1, T2 | β) − k1 T1²`, on nonnegative
innovation levels. -/
noncomputable def innovationPayoff1 (β k1 : ℝ) (T1 T2 : NNReal) : ℝ :=
  grossProfit1 β T1 T2 - k1 * (T1 : ℝ) ^ 2

/-- Manufacturer 2's payoff in the innovation game, `Π*_2(T1, T2 | β) − k2 T2²`. -/
noncomputable def innovationPayoff2 (β k2 : ℝ) (T1 T2 : NNReal) : ℝ :=
  grossProfit2 β T1 T2 - k2 * (T2 : ℝ) ^ 2

/-- `(T1, T2)` is an innovation equilibrium: a pure Nash equilibrium of the innovation game, each
manufacturer's innovation level being a best response over all nonnegative levels. -/
def IsInnovationEquilibrium (β k1 k2 : ℝ) (T1 T2 : NNReal) : Prop :=
  CompetingChains.Cournot.IsPureNash (innovationPayoff1 β k1) (innovationPayoff2 β k2) T1 T2

/-- The downstream outcome at `(T1, T2)` is a duopoly: both manufacturers sell a positive quantity
at the supplier's price. -/
def IsDuopoly (β T1 T2 : ℝ) : Prop :=
  0 < (quantities β T1 T2 (price β T1 T2)).1 ∧ 0 < (quantities β T1 T2 (price β T1 T2)).2

end CrossLicensing.Innovation


