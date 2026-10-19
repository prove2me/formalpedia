-- Prove2me | Definitions.Def_ArtShortage_CashSubsidy_Model
-- name    : ArtShortage_CashSubsidy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:05.390609+00:00
-- url     : https://prove2.me/theorems/c47ee251-38c3-4bc2-b9d8-8a0c82eaed40
-- title:
--   §3–§5.1, pp. 8–16 — two-period trader with budget-adjusting consumers; cash subsidy, eq. (5) welfare, backward induction
-- statement:
--   The model of Levi, Singhvi and Zheng: a monopolist trader sells an essential commodity over two periods to a unit mass of consumers whose Period-1 budgets $b_c$ are uniform on $[0,1]$.
--
--   **Standing assumptions.** The budget adjustment factor satisfies $0<g<4$, and the consumption utility $\lambda$ satisfies $1+g<\lambda$.
--
--   **Base model (§3).** In Period 1 the trader releases $q_1\in[0,1]$, which clears at $p_1=1-q_1$. Consumers perceive the shortage and scale their budgets by
--   $$B(q_1)=1+g(1-q_1).$$
--   Without intervention, Period-2 demand at price $p_2$ is $q_2=1-p_2/B(q_1)$, so $p_2=(1-q_2)B(q_1)$ and the trader's total revenue is
--   $$q_1(1-q_1)+B(q_1)\,q_2(1-q_2),\qquad (q_1,q_2)\in[0,1]^2 .$$
--   **Definition 1** (artificial shortage): $q_1<q_2$ and $p_1<p_2$.
--
--   **Cash subsidy (§4, §5.1).** The government gives cash $c\ge0$ to the fraction $f\in[0,1]$ of consumers with the lowest budgets, subject to $cf\le b$. At Period-2 price $p$, a non-subsidized consumer ($b_c\in[f,1]$) buys iff $b_c\ge p/B(q_1)$, and a subsidized one ($b_c\in[0,f)$) buys iff $b_c\ge(p-c)/B(q_1)$. The numbers of buyers are
--   $$n=\max\{0,\,1-\max(f,p/B)\},\qquad s=\max\{0,\,f-\max(0,(p-c)/B)\},$$
--   and the demand is $D(p)=n+s$.
--
--   1. *Trader, Period 2 (eq. (4)).* He picks $p\ge0$ maximizing $p\,D(p)$; among maximizers, the one with the largest quantity (footnote 10).
--   2. *Welfare (eq. (5)).*
--   $$CW_2=\int_0^{n}(1-q)\,dq+\int_{1-f}^{1-f+s}(1-q)\,dq-p(n+s)+sc+\lambda(n+s)-\lambda\big(1-(n+s)\big).$$
--   3. *Government (eq. (3)).* A feasible $(c,f)$ maximizing $CW_2$ at the trader's best response; among such optima, one with the least outlay $cf$.
--   4. *Trader, Period 1 (eq. (2)).* The equilibrium set $\mathrm{EqQ1}(b)$ consists of the $q_1\in[0,1]$ for which some selection $q\mapsto(c,f,p_2)$ of government choices and Period-2 best responses on $[0,1]$ makes $q_1$ maximize $q(1-q)+p_2D(p_2)$ over $q\in[0,1]$.
--
--   This is the object about which Theorems 1–2 and Proposition 3 are stated.
--
--   **Formalization Note** The trader chooses the Period-2 *price* instead of the quantity. This is equivalent, because demand is non-increasing in price, and it avoids an inverse demand. Purchases at equality count as purchases, as in the text (pp. 8, 15). The added assumption $g<4$ keeps $q_1^*=1/2-g/8$ in $[0,1]$ (the paper's estimate is $g=0.43$). The least-outlay tie-break is necessary. For $b>B(q_1)$, every $c\in[B(q_1),b]$ with $f=1$ attains the same welfare, but the trader's revenue is $c$. Without the rule, Theorem 1(iv)'s $c^*=B(q_1)$ fails and Proposition 3(i)(c) becomes false. The printed formula $s\equiv q_2-p_2/(1+g(1-q_1))$ on p. 16 is not the number of subsidized buyers when none of them buys, so $s$ is taken by its verbal definition ("the number of subsidized consumers who buy").
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), pp. 8–16, §3, Definition 1, §4, §4.1, §5.1, eqs. (2)–(5), footnote 10

import Mathlib

namespace ArtShortage.CashSubsidy

noncomputable section

/-- Standing assumptions of §3–§4 (pp. 10, 13): budget adjustment factor `0 < g`, consumption
utility above the largest updated budget `1 + g < lam`; and the added `g < 4`, which keeps
Proposition 1's `q₁* = 1/2 - g/8` inside `[0, 1]`. -/
def Standing (g lam : ℝ) : Prop := 0 < g ∧ g < 4 ∧ 1 + g < lam

/-- Updated-budget multiplier `1 + g(1 - q₁)` (p. 9): a consumer with Period-1 budget `b_c`
has Period-2 budget `b_c (1 + g(1 - q₁))`. -/
def B (g q1 : ℝ) : ℝ := 1 + g * (1 - q1)

/-- Period-1 market-clearing price `p₁ = 1 - q₁` (p. 9). -/
def p1 (q1 : ℝ) : ℝ := 1 - q1

/-- No intervention, Period-2 inverse demand: `q₂ = 1 - p₂ / (1 + g(1 - q₁))` (p. 10),
i.e. `p₂ = (1 - q₂)(1 + g(1 - q₁))`. -/
def p2NoInt (g q1 q2 : ℝ) : ℝ := (1 - q2) * B g q1

/-- No intervention, the trader's total revenue `q₁(1 - q₁) + (1 + g(1 - q₁)) q₂ (1 - q₂)`
(p. 10, with the printed parenthesis restored). -/
def revNoInt (g q1 q2 : ℝ) : ℝ := q1 * (1 - q1) + B g q1 * q2 * (1 - q2)

/-- `(q₁, q₂) ∈ [0,1]²` maximizes the no-intervention total revenue over `[0,1]²`. -/
def IsNoIntOpt (g q1 q2 : ℝ) : Prop :=
  q1 ∈ Set.Icc (0:ℝ) 1 ∧ q2 ∈ Set.Icc (0:ℝ) 1 ∧
    ∀ q1' ∈ Set.Icc (0:ℝ) 1, ∀ q2' ∈ Set.Icc (0:ℝ) 1, revNoInt g q1' q2' ≤ revNoInt g q1 q2

/-- Definition 1 (p. 9): artificial shortage — less is sold in Period 1 than in Period 2, and
the Period-2 price is nevertheless higher. -/
def IsArtificialShortage (q1 p1 q2 p2 : ℝ) : Prop := q1 < q2 ∧ p1 < p2

/-- Cash subsidy (p. 15): non-subsidized consumers are those with `b_c ∈ [f, 1]`; they buy at
price `p` iff `b_c ≥ p / (1 + g(1 - q₁))`. This is their number. -/
def nonsubBuyers (g q1 f p : ℝ) : ℝ := max 0 (1 - max f (p / B g q1))

/-- Cash subsidy (p. 15): subsidized consumers are those with `b_c ∈ [0, f)`; they buy at
price `p` iff `b_c ≥ (p - c) / (1 + g(1 - q₁))`. This is their number, the `s` of eq. (5). -/
def subBuyers (g q1 c f p : ℝ) : ℝ := max 0 (f - max 0 ((p - c) / B g q1))

/-- Period-2 demand under the cash subsidy `(c, f)` at price `p` (p. 15). -/
def demand (g q1 c f p : ℝ) : ℝ := nonsubBuyers g q1 f p + subBuyers g q1 c f p

/-- Eq. (4), in price form: `p ≥ 0` maximizes the Period-2 revenue `p · D(p)` over all prices
`p' ≥ 0`, and among revenue maximizers it has the largest quantity (footnote 10, p. 16). -/
def IsTraderBR (g q1 c f p : ℝ) : Prop :=
  0 ≤ p ∧ (∀ p', 0 ≤ p' → p' * demand g q1 c f p' ≤ p * demand g q1 c f p) ∧
    (∀ p', 0 ≤ p' → p' * demand g q1 c f p' = p * demand g q1 c f p →
      demand g q1 c f p' ≤ demand g q1 c f p)

/-- Eq. (5), p. 16: Period-2 consumer welfare under the cash subsidy `(c, f)` when the trader
charges `p`, with `p₁(q) = 1 - q`; `n` non-subsidized and `s` subsidized consumers buy. -/
def CW2 (g lam q1 c f p : ℝ) : ℝ :=
  let n := nonsubBuyers g q1 f p
  let s := subBuyers g q1 c f p
  (∫ q in (0:ℝ)..n, (1 - q)) + (∫ q in (1 - f)..(1 - f + s), (1 - q))
    - p * (n + s) + s * c + lam * (n + s) - lam * (1 - (n + s))

/-- Feasible cash-subsidy policies: amount `c ≥ 0`, fraction `f ∈ [0, 1]`, outlay `c f ≤ b`
(eq. (3)). -/
def Feasible (b c f : ℝ) : Prop := 0 ≤ c ∧ 0 ≤ f ∧ f ≤ 1 ∧ c * f ≤ b

/-- Eq. (3): `(c, f)` is feasible and maximizes the Period-2 welfare `CW2`, evaluated at the
trader's Period-2 best response, over all feasible policies. -/
def IsGovOpt (g lam b q1 c f : ℝ) : Prop :=
  Feasible b c f ∧ ∃ p, IsTraderBR g q1 c f p ∧
    ∀ c' f' p', Feasible b c' f' → IsTraderBR g q1 c' f' p' →
      CW2 g lam q1 c' f' p' ≤ CW2 g lam q1 c f p

/-- The government's choice: a welfare-optimal policy with the least outlay `c f` among all
welfare-optimal policies (the tie-break that yields Theorem 1(iv)'s `c* = 1 + g(1 - q₁)`). -/
def IsGovChoice (g lam b q1 c f : ℝ) : Prop :=
  IsGovOpt g lam b q1 c f ∧ ∀ c' f', IsGovOpt g lam b q1 c' f' → c * f ≤ c' * f'

/-- Eq. (2): the trader's total revenue `q₁(1 - q₁) + p₂ q₂` when, after `q₁`, the government
plays `x.1 = c`, `x.2.1 = f` and the trader charges `x.2.2 = p₂` in Period 2. -/
def totalRev (g q1 : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  q1 * (1 - q1) + x.2.2 * demand g q1 x.1 x.2.1 x.2.2

/-- The CS equilibrium Period-1 quantities (backward induction, eqs. (2)–(4)): `q₁ ∈ [0, 1]`
such that for some selection `σ q = (c, f, p₂)` of a government choice and a Period-2 best
response at every `q ∈ [0, 1]`, `q₁` maximizes the total revenue against `σ`. -/
def EqQ1 (g lam b : ℝ) : Set ℝ :=
  {q1 | q1 ∈ Set.Icc (0:ℝ) 1 ∧ ∃ σ : ℝ → ℝ × ℝ × ℝ,
    (∀ q ∈ Set.Icc (0:ℝ) 1, IsGovChoice g lam b q (σ q).1 (σ q).2.1 ∧
      IsTraderBR g q (σ q).1 (σ q).2.1 (σ q).2.2) ∧
    ∀ q ∈ Set.Icc (0:ℝ) 1, totalRev g q (σ q) ≤ totalRev g q1 (σ q1)}

end

end ArtShortage.CashSubsidy


