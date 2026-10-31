-- Prove2me | Definitions.Def_LongShortSI_Model
-- name    : LongShortSI_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:37.81362+00:00
-- url     : https://prove2.me/theorems/26774614-bb37-4e9e-ac22-324fd69e40f3
-- title:
--   Two suppliers, one non-exclusive reseller, two periods with inventory: demand (1), profits (3)–(4), the LL and SS games and their subgame-perfect equilibria
-- statement:
--   Two suppliers $A$ and $B$ sell partially substitutable products through one reseller over two periods $t\in\{1,2\}$. For product $i$ with rival product $j\ne i$, the market-clearing price in period $t$ is the inverse demand (1)
--   $$
--   p_{it}=a-s_{it}-d\,s_{jt},\qquad a>0,\ 0\le d<1,
--   $$
--   where $s_{it}$ is the quantity of product $i$ the reseller sells in period $t$. The reseller buys $q_{i1}$ units of $i$ in period 1, sells $s_{i1}$ of them and carries $I_i=q_{i1}-s_{i1}$ into period 2 at unit holding cost $h$; in period 2 she buys $q_{i2}$ and sells all her stock, $s_{i2}=q_{i2}+I_i$. Her profit (3) and supplier $i$'s profit (4) are
--   $$
--   \pi=\sum_{i\in\{A,B\}}\bigl(p_{i1}s_{i1}-w_{i1}q_{i1}-hI_i+p_{i2}s_{i2}-w_{i2}q_{i2}\bigr),\qquad \Pi_i=w_{i1}q_{i1}+w_{i2}q_{i2}.
--   $$
--
--   1. **LL game** (both suppliers offer long-term contracts, Table 1). The suppliers simultaneously offer $(w_{i1},w_{i2})\ge 0$; the reseller, seeing all four prices, commits to $(s_{i1},I_i,q_{i2})\ge0$ for both products. A profile is a subgame-perfect equilibrium when the reseller's plan maximizes $\pi$ at **every** non-negative price quadruple and the offers form a pure Nash equilibrium of the suppliers' game given that response.
--   2. **SS game** (both offer short-term contracts). The suppliers simultaneously offer $w_{i1}\ge0$; the reseller chooses $(s_{i1},I_i)\ge0$; the suppliers, seeing $(I_A,I_B)$, simultaneously offer $w_{i2}\ge0$; the reseller buys $q_{i2}\ge0$. A profile is a subgame-perfect equilibrium when the purchases are optimal after every $(I,w_2)$, the period-2 prices are a Nash equilibrium after every $I$, the period-1 decision is optimal after every $w_1$ given the continuation, and the period-1 prices are a Nash equilibrium given everything after.
--
--   The outcome of a profile records the on-path prices, purchases, sales, inventories, $\Pi_i$ and $\pi$ (the entries of Table 2). These are the primitives of every equilibrium statement of the mission; no closed form of the paper is used to define them.
--
--   **Formalization Note** The two stage games use the published two-player pure-Nash predicate `CompetingChains.Cournot.IsPureNash` with strategy types $\mathbb R_{\ge0}$ (SS) and $\mathbb R_{\ge0}^2$ (LL). Period-2 strategies of the SS game take the inventories (and, for the reseller, the period-2 prices) as their history. No floor is put on market prices: a large inventory, sold in full in period 2, can make $p_{i2}$ negative off the equilibrium path, as in the paper's model. The period-2 reseller objective is the period-2 part of (3); the printed (EC.1) has $(q_{j2}+I_j)$ in place of $(q_{i2}+I_i)$.
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), §3 The Model, p.6 (demand (1), balance equations); §3.1 and Table 1, pp.7–9 (move orders of LL and SS); §4, (3)–(4), p.9; E-Companion EC.1, ec1–ec4 (PDF 33–36), (EC.1)–(EC.7)

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

open scoped NNReal

namespace LongShortSI

/-- The two products (and their suppliers) `A` and `B`.
Roy–Gilbert–Lai, *The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply
Contracts in Nonexclusive Reselling Environments*, SSRN 3752131 (version of 2022-04-20), §3, p.6. -/
inductive Product where
  | A
  | B
  deriving DecidableEq

/-- The other product: `j ≠ i`. -/
def Product.other : Product → Product
  | .A => .B
  | .B => .A

/-- The function on products taking the value `xA` at `A` and `xB` at `B`. -/
def pair {α : Type*} (xA xB : α) : Product → α
  | .A => xA
  | .B => xB

/-- Every entry of a vector indexed by the two products is non-negative. -/
def Nonneg (f : Product → ℝ) : Prop := ∀ i, 0 ≤ f i

/-- The deterministic inverse demand (1), SSRN 3752131 (version of 2022-04-20), §3, p.6:
`p_it = a − s_it − d·s_jt` for `i ∈ {A, B}`, `j ≠ i`, where `s` are the period's sales.

**Formalization Note** No sign restriction is put on the market price: off the equilibrium path a
large inventory, all of which is sold in period 2, can drive it negative, as in the paper's model. -/
def marketPrice (a d : ℝ) (s : Product → ℝ) (i : Product) : ℝ := a - s i - d * s i.other

/-- A complete quantity plan of the reseller (§3, pp.6–8): first-period sales `s_i1`, inventories
`I_i` carried into period 2, and second-period purchases `q_i2`. The first-period purchase is
`q_i1 = s_i1 + I_i` and the second-period sale is `s_i2 = q_i2 + I_i` (all stock is sold, "no
units are salvaged", p.6). -/
structure Plan where
  s1 : Product → ℝ
  inv : Product → ℝ
  q2 : Product → ℝ

namespace Plan

/-- First-period purchases `q_i1 = s_i1 + I_i` (p.6). -/
def q1 (x : Plan) (i : Product) : ℝ := x.s1 i + x.inv i

/-- Second-period sales `s_i2 = q_i2 + I_i` (p.6). -/
def s2 (x : Plan) (i : Product) : ℝ := x.q2 i + x.inv i

/-- All quantities are non-negative (`s_i1, I_i, q_i2 ≥ 0`, hence `q_i1, s_i2 ≥ 0`), p.8. -/
def Feasible (x : Plan) : Prop := ∀ i, 0 ≤ x.s1 i ∧ 0 ≤ x.inv i ∧ 0 ≤ x.q2 i

end Plan

/-- The four wholesale prices `w_it`, `i ∈ {A, B}`, `t ∈ {1, 2}`. -/
structure Prices where
  w1 : Product → ℝ
  w2 : Product → ℝ

/-- Wholesale prices are non-negative. -/
def Prices.Nonneg (w : Prices) : Prop := ∀ i, 0 ≤ w.w1 i ∧ 0 ≤ w.w2 i

/-- One product's term of the reseller's profit (3):
`p_i1 s_i1 − w_i1 q_i1 − h I_i + p_i2 s_i2 − w_i2 q_i2`. -/
def resellerTerm (a d h : ℝ) (w : Prices) (x : Plan) (i : Product) : ℝ :=
  marketPrice a d x.s1 i * x.s1 i - w.w1 i * x.q1 i - h * x.inv i
    + marketPrice a d x.s2 i * x.s2 i - w.w2 i * x.q2 i

/-- The reseller's total profit (3), SSRN 3752131 (version of 2022-04-20), §4, p.9:
`π = Σ_{i ∈ {A,B}} (p_i1 s_i1 − w_i1 q_i1 − h I_i + p_i2 s_i2 − w_i2 q_i2)`, with `p_it` from (1),
`q_i1 = s_i1 + I_i`, `q_i2 = s_i2 − I_i`. Marginal selling costs are zero (p.6). -/
def resellerProfit (a d h : ℝ) (w : Prices) (x : Plan) : ℝ :=
  resellerTerm a d h w x .A + resellerTerm a d h w x .B

/-- Supplier `i`'s profit (4), §4, p.9: `Π_i = w_i1 q_i1 + w_i2 q_i2` (production cost zero, p.6). -/
def supplierProfit (w : Prices) (x : Plan) (i : Product) : ℝ := w.w1 i * x.q1 i + w.w2 i * x.q2 i

/-- The on-path outcome record of a play, the entries reported in Table 2 (p.28): wholesale prices,
purchases, sales, inventories, the suppliers' profits `Π_i` and the reseller's profit `π`. -/
structure Outcome where
  w1 : Product → ℝ
  w2 : Product → ℝ
  q1 : Product → ℝ
  q2 : Product → ℝ
  s1 : Product → ℝ
  s2 : Product → ℝ
  inv : Product → ℝ
  supplier : Product → ℝ
  reseller : ℝ

/-- The outcome record of the play with prices `w` and plan `x`. -/
def outcomeOf (a d h : ℝ) (w : Prices) (x : Plan) : Outcome :=
  ⟨w.w1, w.w2, x.q1, x.q2, x.s1, x.s2, x.inv, supplierProfit w x, resellerProfit a d h w x⟩

/-! ### The LL game (§4.1, Table 1 column LL, p.9) -/

/-- A supplier's offer under a long-term contract: `(w_i1, w_i2)`, both non-negative. -/
abbrev LLOffer := ℝ≥0 × ℝ≥0

/-- The four prices when supplier `A` offers `xA` and supplier `B` offers `xB`. -/
def llPrices (xA xB : LLOffer) : Prices :=
  ⟨pair (xA.1 : ℝ) (xB.1 : ℝ), pair (xA.2 : ℝ) (xB.2 : ℝ)⟩

/-- A strategy profile of the LL game (§4.1, p.9; Table 1, column LL):
1. (stage 1a) suppliers `A` and `B` simultaneously offer `(w_A1, w_A2)` and `(w_B1, w_B2)`;
2. (stage 1b) the reseller, observing all four prices, commits to her whole plan
   `(s_i1, I_i, q_i2)` for both products (`resp`). There is no period-2 decision. -/
structure LLProfile where
  offerA : LLOffer
  offerB : LLOffer
  resp : Prices → Plan

namespace LLProfile

/-- The reseller's plan is optimal after every non-negative price quadruple: it is feasible and
maximizes `π` (3) over all feasible plans. -/
def ResellerOptimal (a d h : ℝ) (σ : LLProfile) : Prop :=
  ∀ w : Prices, w.Nonneg →
    (σ.resp w).Feasible ∧
    ∀ x : Plan, x.Feasible → resellerProfit a d h w x ≤ resellerProfit a d h w (σ.resp w)

/-- Supplier `i`'s payoff in the stage-1a pricing game, given the reseller's strategy. -/
def payoff (σ : LLProfile) (i : Product) (xA xB : LLOffer) : ℝ :=
  supplierProfit (llPrices xA xB) (σ.resp (llPrices xA xB)) i

/-- Pure subgame-perfect equilibrium of the LL game with demand parameter `a`, substitutability
`d` and holding cost `h` (§4.1, p.9): the reseller's plan is optimal at every price quadruple, and
the suppliers' offers form a pure Nash equilibrium of the stage-1a game over all non-negative
offers, given the reseller's strategy.

**Formalization Note** Wholesale prices range over `[0, ∞)`; the stage-1a game uses the published
two-player predicate `CompetingChains.Cournot.IsPureNash` with strategy type `ℝ≥0 × ℝ≥0`. -/
def IsSPE (a d h : ℝ) (σ : LLProfile) : Prop :=
  σ.ResellerOptimal a d h ∧
  CompetingChains.Cournot.IsPureNash (σ.payoff .A) (σ.payoff .B) σ.offerA σ.offerB

/-- The on-path outcome of an LL profile. -/
def outcome (a d h : ℝ) (σ : LLProfile) : Outcome :=
  outcomeOf a d h (llPrices σ.offerA σ.offerB) (σ.resp (llPrices σ.offerA σ.offerB))

end LLProfile

/-! ### The SS game (§4.2, Table 1 column SS, pp.8–9; E-Companion EC.1, ec1–ec4) -/

/-- The reseller's first-period decision under short-term contracts: sales `s_i1` and
inventories `I_i` (so `q_i1 = s_i1 + I_i`). -/
structure Stock where
  s1 : Product → ℝ
  inv : Product → ℝ

/-- First-period sales and inventories are non-negative. -/
def Stock.Feasible (y : Stock) : Prop := ∀ i, 0 ≤ y.s1 i ∧ 0 ≤ y.inv i

/-- The reseller's period-2 profit, the period-2 part of (3) (§4, p.9), given inventories `I`,
second-period prices `w2` and purchases `q`: `Σ_i (p_i2 s_i2 − w_i2 q_i2)` with
`s_i2 = q_i2 + I_i`.

**Formalization Note** This is the period-2 part of (3). The printed (EC.1), ec1, multiplies the
price of product `i` by `(q_j2 + I_j)` instead of `(q_i2 + I_i)` (correction C6). -/
def resellerProfit2 (a d : ℝ) (I w2 q : Product → ℝ) : ℝ :=
  (marketPrice a d (fun k => q k + I k) .A * (q .A + I .A) - w2 .A * q .A)
    + (marketPrice a d (fun k => q k + I k) .B * (q .B + I .B) - w2 .B * q .B)

/-- Stage 2b: after every non-negative inventory vector `I` and every non-negative pair of
second-period prices `w2`, the reseller's purchases `resp2 I w2` are non-negative and maximize her
period-2 profit over all non-negative purchases. -/
def Stage2bOptimal (a d : ℝ) (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ)) : Prop :=
  ∀ I, Nonneg I → ∀ w2, Nonneg w2 →
    Nonneg (resp2 I w2) ∧
    ∀ q, Nonneg q → resellerProfit2 a d I w2 q ≤ resellerProfit2 a d I w2 (resp2 I w2)

/-- Supplier `i`'s payoff in the stage-2a pricing game at inventories `I`, given the reseller's
stage-2b strategy: `w_i2 · q_i2` ((EC.3), ec1). -/
def stage2Payoff (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ)) (I : Product → ℝ)
    (i : Product) (wA wB : ℝ≥0) : ℝ :=
  pair (wA : ℝ) (wB : ℝ) i * resp2 I (pair (wA : ℝ) (wB : ℝ)) i

/-- Stage 2a: after every non-negative inventory vector `I`, the second-period prices
`price2 I = (w_A2, w_B2)` form a pure Nash equilibrium of the suppliers' pricing game over all
non-negative prices, given the reseller's stage-2b strategy. -/
def Stage2aNash (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ))
    (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) : Prop :=
  ∀ I, Nonneg I →
    CompetingChains.Cournot.IsPureNash (stage2Payoff resp2 I .A) (stage2Payoff resp2 I .B)
      (price2 I).1 (price2 I).2

/-- The second-period prices chosen at inventories `I`, as a vector. -/
def price2Fun (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) (I : Product → ℝ) : Product → ℝ :=
  pair ((price2 I).1 : ℝ) ((price2 I).2 : ℝ)

/-- The complete plan after the first-period decision `y`, continuation strategies followed. -/
def planAfter (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ))
    (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) (y : Stock) : Plan :=
  ⟨y.s1, y.inv, resp2 y.inv (price2Fun price2 y.inv)⟩

/-- The four prices after first-period prices `w1` and first-period decision `y`. -/
def pricesAfter (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) (w1 : Product → ℝ) (y : Stock) : Prices :=
  ⟨w1, price2Fun price2 y.inv⟩

/-- The reseller's total profit (3) after first-period prices `w1` and first-period decision `y`,
with the continuation `(price2, resp2)` ((EC.5), ec3). -/
def ssResellerTotal (a d h : ℝ) (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ))
    (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) (w1 : Product → ℝ) (y : Stock) : ℝ :=
  resellerProfit a d h (pricesAfter price2 w1 y) (planAfter resp2 price2 y)

/-- Stage 1b: `y` is a best response of the reseller to first-period prices `w1`, given the
continuation: it is feasible and maximizes her total profit over all feasible first-period
decisions. -/
def Period1BestResponse (a d h : ℝ) (resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ))
    (price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0) (w1 : Product → ℝ) (y : Stock) : Prop :=
  y.Feasible ∧ ∀ z : Stock, z.Feasible →
    ssResellerTotal a d h resp2 price2 w1 z ≤ ssResellerTotal a d h resp2 price2 w1 y

/-- A strategy profile of the SS game (§3.1, pp.7–8; Table 1, column SS):
1. (stage 1a) suppliers simultaneously offer `w_A1`, `w_B1` (`w1A`, `w1B`);
2. (stage 1b) the reseller, observing them, chooses `(s_i1, I_i)` (`resp1 w1`);
3. (stage 2a) the suppliers, observing the inventories `(I_A, I_B)`, simultaneously offer
   `(w_A2, w_B2)` (`price2 I`);
4. (stage 2b) the reseller, observing `I` and `w2`, purchases `q_i2` (`resp2 I w2`).

**Formalization Note** Period-2 strategies take the inventories (and, for the reseller, the
second-period prices) as their history: the suppliers observe the reseller's inventory (§3.1, p.8),
and the period-2 payoffs depend on nothing else. -/
structure SSProfile where
  w1A : ℝ≥0
  w1B : ℝ≥0
  resp1 : (Product → ℝ) → Stock
  price2 : (Product → ℝ) → ℝ≥0 × ℝ≥0
  resp2 : (Product → ℝ) → (Product → ℝ) → (Product → ℝ)

namespace SSProfile

/-- Supplier `i`'s two-period profit (4) when the first-period prices are `(wA, wB)`, all later
moves following `σ` ((EC.7), ec4). -/
def payoff (σ : SSProfile) (i : Product) (wA wB : ℝ≥0) : ℝ :=
  supplierProfit (pricesAfter σ.price2 (pair (wA : ℝ) (wB : ℝ)) (σ.resp1 (pair (wA : ℝ) (wB : ℝ))))
    (planAfter σ.resp2 σ.price2 (σ.resp1 (pair (wA : ℝ) (wB : ℝ)))) i

/-- Pure subgame-perfect equilibrium of the SS game with parameters `a`, `d`, `h`
(§4.2, pp.10–11; ec1–ec4). Every action is optimal at every history:
1. stage 2b: the reseller's purchases are optimal after every `I ≥ 0`, `w2 ≥ 0`;
2. stage 2a: the second-period prices are a Nash equilibrium after every `I ≥ 0`;
3. stage 1b: the reseller's `(s_1, I)` is a best response after every `w1 ≥ 0`, given 1–2;
4. stage 1a: the first-period prices are a Nash equilibrium of the suppliers' game over all
   non-negative prices, given 1–3.

**Formalization Note** Wholesale prices range over `[0, ∞)`; the stage games use the published
two-player predicate `CompetingChains.Cournot.IsPureNash` with strategy type `ℝ≥0`. -/
def IsSPE (a d h : ℝ) (σ : SSProfile) : Prop :=
  Stage2bOptimal a d σ.resp2 ∧
  Stage2aNash σ.resp2 σ.price2 ∧
  (∀ w1 : Product → ℝ, Nonneg w1 → Period1BestResponse a d h σ.resp2 σ.price2 w1 (σ.resp1 w1)) ∧
  CompetingChains.Cournot.IsPureNash (σ.payoff .A) (σ.payoff .B) σ.w1A σ.w1B

/-- The on-path first-period prices. -/
def w1 (σ : SSProfile) : Product → ℝ := pair (σ.w1A : ℝ) (σ.w1B : ℝ)

/-- The on-path outcome of an SS profile. -/
def outcome (a d h : ℝ) (σ : SSProfile) : Outcome :=
  outcomeOf a d h (pricesAfter σ.price2 σ.w1 (σ.resp1 σ.w1)) (planAfter σ.resp2 σ.price2 (σ.resp1 σ.w1))

end SSProfile

end LongShortSI


