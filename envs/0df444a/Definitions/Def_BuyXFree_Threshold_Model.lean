-- Prove2me | Definitions.Def_BuyXFree_Threshold_Model
-- name    : BuyXFree_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:45.980207+00:00
-- url     : https://prove2.me/theorems/bd92e42c-b8e4-4339-b371-4f1242e63dcb
-- title:
--   §3–§4.1, pp. 6–12 — BXGO consumer dynamic program (1)–(2), decisions, induced point-inventory chain, long-run revenue; A, A₁, p^B, p^D
-- statement:
--   A monopolist sells a nondurable product at a fixed price $p$ with a "Buy $X$, get one free" (BXGO) reward program: a consumer earns one point per purchase, and with $X\ge1$ points she is eligible for a free unit. The marginal cost is normalised to $0$, so revenue and profit coincide.
--
--   **Consumer.** In each period the consumer is in the market with probability $\lambda$. In the market she values the product at $v$ and faces an outside option $v_0\in\{0,\bar v\}$, equal to $0$ with probability $q$; a redemption gives her an extra transaction utility $k\ge0$. She discounts with $\delta\in(0,1)$. The standing assumptions are
--   $$0\le\lambda\le1,\quad 0\le q\le1,\quad 0<\delta<1,\quad v\ge\bar v\ge0,\quad k\ge0 .$$
--
--   **Optimality equations.** A function $J$ on the point inventories $\{0,\dots,X\}$ is a value function of the program $(p,X)$ when
--   $$J(x)=\lambda q\max\{v-p+\delta J(x+1),\,\delta J(x)\}+\lambda(1-q)\max\{v-p+\delta J(x+1),\,\bar v+\delta J(x)\}+(1-\lambda)\delta J(x),\quad x=0,\dots,X-1,\qquad(1)$$
--   $$J(X)=\lambda q\max\{v+k+\delta J(0),\,\delta J(X)\}+\lambda(1-q)\max\{v+k+\delta J(0),\,\bar v+\delta J(X)\}+(1-\lambda)\delta J(X).\qquad(2)$$
--
--   **Decisions.** With outside option $0$ she buys in state $x<X$ when $v-p+\delta J(x+1)\ge\delta J(x)$, and with outside option $\bar v$ when $v-p+\delta J(x+1)\ge\bar v+\delta J(x)$; in state $X$ she redeems when $v+k+\delta J(0)\ge\delta J(X)$, respectively $v+k+\delta J(0)\ge\bar v+\delta J(X)$. Ties are resolved in favour of buying or redeeming.
--
--   **Induced chain and profit.** These decisions make the point inventory a Markov chain on $\{0,\dots,X\}$: from $x<X$ it moves to $x+1$ with probability $\lambda\,(q\,\mathbf 1[\text{buys at }0]+(1-q)\,\mathbf 1[\text{buys at }\bar v])$ and stays otherwise, and from $X$ it moves to $0$ with the analogous redemption probability. The purchase probability in state $x<X$ is the probability of moving; in state $X$ it is $0$ (a redemption is not a purchase), and the expected revenue in a period is $p$ times the purchase probability. For a consumer who starts with $0$ points, the average expected revenue over the first $N$ periods is
--   $$\bar R_N=\frac1N\sum_{n=0}^{N-1}\mathbb E[\text{revenue in period }n].$$
--   The comparison profit of a firm without a reward program is $\max\{\lambda qv,\lambda(v-\bar v)\}$.
--
--   **Constants** (p. 10). $A=\dfrac{\lambda q\delta}{1-\delta+\lambda q\delta}$, $A_1=\dfrac{\lambda\delta}{1-\delta+\lambda\delta}$, and for $0\le\tau\le X$
--   $$p^B(\tau)=\frac{q(1-A^\tau A_1^{X-\tau+1})v+(1-q)A^\tau(1-A_1^{X-\tau+1})(v-\bar v)+A^\tau A_1^{X-\tau}(1-A_1)k}{A^\tau(1-A_1^{X-\tau})+q(1-A^\tau)},$$
--   $$p^D(\tau)=\frac{\bigl(1-A_1^{X-\tau+1}+q(1-A^\tau)A_1^{X-\tau+1}\bigr)(v-\bar v)+A_1^{X-\tau}(1-A_1)k}{1-A_1^{X-\tau}+q(1-A^\tau)A_1^{X-\tau+1}},$$
--   and the upper price of Proposition 2(d) is $\dfrac{(1-A^{X+1})v+A^X(1-A)k}{1-A^X}$. The file also names the case (b) behaviour with threshold $\tau$ (buy in every state at outside option $0$, buy exactly in the states $\tau\le x<X$ at outside option $\bar v$, redeem under both) and the case (c) behaviour (buy at outside option $0$ only, redeem under both).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** `Params` bundles $(\lambda,q,\delta,v,\bar v,k)$ (`lam` stands for $\lambda$); `Params.Standing` is the list of standing assumptions. The value function is not defined: `IsValueFn P p X J` states that `J : ℕ → ℝ` satisfies (1) for $x<X$ and (2); the operator of (1)–(2) is a $\delta$-contraction in the sup norm, so exactly one such $J$ exists on $\{0,\dots,X\}$, and values beyond $X$ are irrelevant. States of the chain are `Fin (X+1)`; `trans` is the transition matrix (rows sum to $1$), `buyProb` the purchase probability, `revenue` $=p\cdot$`buyProb`, `distAt n` the law after $n$ periods from state $0$, and `avgRevenue N` $=\bar R_N$. Stationary distributions use the published `MarkovChain.IsStationary` (a probability vector $\mu$ with $\mu P=\mu$). In `pB`, `pD` the exponents use natural-number subtraction, exact for $\tau\le X$; divisions follow Lean's convention $x/0=0$, so statements that need nonvanishing denominators carry $\lambda>0$, $q>0$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), pp. 6–12, §3, §3.1 (equations (1)–(2), p. 8), p. 10 (A, A₁, p^B, p^D, Proposition 2(d)), §4.1 pp. 11–12 (Figure 1, the induced chain and the comparison profit)

import Mathlib
import Definitions.Def_MarkovChain

namespace BuyXFree.Threshold

open Matrix

/-- Consumer parameters of the BXGO model, §3, pp. 6–8: `lam` = λ (market-arrival probability),
`q` (probability that the outside option is `0`), `δ` (discount factor), `v` (valuation),
`vbar` = v̄ (high outside option), `k` (transaction utility of a redemption). -/
structure Params where
  lam : ℝ
  q : ℝ
  δ : ℝ
  v : ℝ
  vbar : ℝ
  k : ℝ

/-- Standing assumptions of §3, p. 7: `λ, q ∈ [0,1]`, `δ ∈ (0,1)`, `v ≥ v̄ ≥ 0`, `k ≥ 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 ≤ P.lam ∧ P.lam ≤ 1 ∧ 0 ≤ P.q ∧ P.q ≤ 1 ∧ 0 < P.δ ∧ P.δ < 1 ∧
    0 ≤ P.vbar ∧ P.vbar ≤ P.v ∧ 0 ≤ P.k

/-- `A = λqδ / (1 − δ + λqδ)`, p. 10. -/
noncomputable def A (P : Params) : ℝ := P.lam * P.q * P.δ / (1 - P.δ + P.lam * P.q * P.δ)

/-- `A₁ = λδ / (1 − δ + λδ)`, p. 10. -/
noncomputable def A1 (P : Params) : ℝ := P.lam * P.δ / (1 - P.δ + P.lam * P.δ)

/-- `J` solves the optimality equations (1) (states `x = 0, …, X − 1`) and (2) (state `X`), p. 8,
of the consumer facing the BXGO program with price `p` and redemption threshold `X`.
Values of `J` beyond `X` play no role. -/
def IsValueFn (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) : Prop :=
  (∀ x < X, J x = P.lam * P.q * max (P.v - p + P.δ * J (x + 1)) (P.δ * J x)
      + P.lam * (1 - P.q) * max (P.v - p + P.δ * J (x + 1)) (P.vbar + P.δ * J x)
      + (1 - P.lam) * P.δ * J x) ∧
  J X = P.lam * P.q * max (P.v + P.k + P.δ * J 0) (P.δ * J X)
      + P.lam * (1 - P.q) * max (P.v + P.k + P.δ * J 0) (P.vbar + P.δ * J X)
      + (1 - P.lam) * P.δ * J X

/-- With outside option `0`, the consumer in state `x` buys: `v − p + δJ(x+1) ≥ δJ(x)`
(ties go to buying). -/
def BuysLow (P : Params) (p : ℝ) (J : ℕ → ℝ) (x : ℕ) : Prop :=
  P.δ * J x ≤ P.v - p + P.δ * J (x + 1)

/-- With outside option `v̄`, the consumer in state `x` buys: `v − p + δJ(x+1) ≥ v̄ + δJ(x)`
(ties go to buying). -/
def BuysHigh (P : Params) (p : ℝ) (J : ℕ → ℝ) (x : ℕ) : Prop :=
  P.vbar + P.δ * J x ≤ P.v - p + P.δ * J (x + 1)

/-- With outside option `0`, the consumer in state `X` redeems: `v + k + δJ(0) ≥ δJ(X)`. -/
def RedeemsLow (P : Params) (X : ℕ) (J : ℕ → ℝ) : Prop :=
  P.δ * J X ≤ P.v + P.k + P.δ * J 0

/-- With outside option `v̄`, the consumer in state `X` redeems: `v + k + δJ(0) ≥ v̄ + δJ(X)`. -/
def RedeemsHigh (P : Params) (X : ℕ) (J : ℕ → ℝ) : Prop :=
  P.vbar + P.δ * J X ≤ P.v + P.k + P.δ * J 0

open Classical in
/-- Probability that the consumer leaves state `x` in one period: she is in the market
(probability λ) and buys (`x < X`) or redeems (`x = X`) given the realised outside option. -/
noncomputable def moveProb (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (x : ℕ) : ℝ :=
  if x < X then
    P.lam * (P.q * (if BuysLow P p J x then 1 else 0)
      + (1 - P.q) * (if BuysHigh P p J x then 1 else 0))
  else
    P.lam * (P.q * (if RedeemsLow P X J then 1 else 0)
      + (1 - P.q) * (if RedeemsHigh P X J then 1 else 0))

/-- Successor in the point-inventory cycle: `x ↦ x + 1` for `x < X`, and `X ↦ 0`. -/
def nextState (X : ℕ) (i : Fin (X + 1)) : Fin (X + 1) :=
  if h : i.val < X then ⟨i.val + 1, by omega⟩ else 0

/-- Transition matrix of the point inventory induced by the decisions of `J` (§4.1, p. 12):
from state `i` the chain moves to `nextState X i` with probability `moveProb` and stays
otherwise. -/
noncomputable def trans (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) :
    Matrix (Fin (X + 1)) (Fin (X + 1)) ℝ := fun i j =>
  (if j = nextState X i then moveProb P p X J i else 0) +
    (if j = i then 1 - moveProb P p X J i else 0)

/-- Purchase probability in a period spent in state `i`: `moveProb` below the threshold;
a redemption in state `X` is not a purchase. -/
noncomputable def buyProb (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (i : Fin (X + 1)) : ℝ :=
  if i.val < X then moveProb P p X J i else 0

/-- Expected revenue in a period spent in state `i`: price times purchase probability
(marginal cost is normalised to `0`, p. 6). -/
noncomputable def revenue (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (i : Fin (X + 1)) : ℝ :=
  p * buyProb P p X J i

/-- Distribution of the point inventory after `n` periods, for a consumer who starts with
`0` points. -/
noncomputable def distAt (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (n : ℕ) : Fin (X + 1) → ℝ :=
  Pi.single (0 : Fin (X + 1)) (1 : ℝ) ᵥ* (trans P p X J ^ n)

/-- Average expected revenue per period over the first `N` periods, for a consumer who starts
with `0` points. -/
noncomputable def avgRevenue (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, distAt P p X J n ⬝ᵥ revenue P p X J) / N

/-- The firm's profit without a reward program, `max{λqv, λ(v − v̄)}` (pp. 11–12, 25). -/
noncomputable def noProgramProfit (P : Params) : ℝ :=
  max (P.lam * P.q * P.v) (P.lam * (P.v - P.vbar))

/-- The boundary price `p^B(τ)`, p. 10 (used for `1 ≤ τ ≤ X`). -/
noncomputable def pB (P : Params) (X τ : ℕ) : ℝ :=
  (P.q * (1 - A P ^ τ * A1 P ^ (X - τ + 1)) * P.v
      + (1 - P.q) * A P ^ τ * (1 - A1 P ^ (X - τ + 1)) * (P.v - P.vbar)
      + A P ^ τ * A1 P ^ (X - τ) * (1 - A1 P) * P.k)
    / (A P ^ τ * (1 - A1 P ^ (X - τ)) + P.q * (1 - A P ^ τ))

/-- The boundary price `p^D(τ)`, p. 10 (used for `0 ≤ τ ≤ X`). -/
noncomputable def pD (P : Params) (X τ : ℕ) : ℝ :=
  ((1 - A1 P ^ (X - τ + 1) + P.q * (1 - A P ^ τ) * A1 P ^ (X - τ + 1)) * (P.v - P.vbar)
      + A1 P ^ (X - τ) * (1 - A1 P) * P.k)
    / (1 - A1 P ^ (X - τ) + P.q * (1 - A P ^ τ) * A1 P ^ (X - τ + 1))

/-- The upper price of Proposition 2(d), `((1 − A^{X+1})v + A^X(1 − A)k)/(1 − A^X)`, p. 10. -/
noncomputable def pdUpper (P : Params) (X : ℕ) : ℝ :=
  ((1 - A P ^ (X + 1)) * P.v + A P ^ X * (1 - A P) * P.k) / (1 - A P ^ X)

/-- Case (b) behaviour with threshold `τ` (§4.1, p. 11): with outside option `0` she buys in
every state below `X`; with outside option `v̄` she buys exactly in the states `τ ≤ x < X`;
she redeems in state `X` under either outside option. -/
def CaseB (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (τ : ℕ) : Prop :=
  (∀ x < X, BuysLow P p J x ∧ (BuysHigh P p J x ↔ τ ≤ x)) ∧ RedeemsLow P X J ∧ RedeemsHigh P X J

/-- Case (c) behaviour (§4.1, p. 11): with outside option `0` she buys in every state below `X`;
with outside option `v̄` she never buys; she redeems in state `X` under either outside option. -/
def CaseC (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) : Prop :=
  (∀ x < X, BuysLow P p J x ∧ ¬ BuysHigh P p J x) ∧ RedeemsLow P X J ∧ RedeemsHigh P X J

end BuyXFree.Threshold


