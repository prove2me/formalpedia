-- Prove2me | Definitions.Def_ImperfectTargeting_CostlessAds_Setting
-- name    : ImperfectTargeting_CostlessAds_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:59.165896+00:00
-- url     : https://prove2.me/theorems/6f3710a5-09fa-44b3-a15d-7d8dbeecb843
-- title:
--   §3, §4.1–§4.2, pp. 7–15 — the targeting-and-pricing game: groups, scopes, reach, subgame payoffs, SPNE, cdfs (1) and (2), thresholds α̂₁, α̂₂
-- statement:
--   This file defines the two-stage game of Karle and Reisinger's model of advertising with imperfect targeting (§3), built on the clearinghouse pricing game.
--
--   **Consumers and firms.** There are two consumer groups, $a$ and $b$, each of mass one. Group-$b$ consumers value the product at $1$, group-$a$ consumers at $A$, with $0 < A < 1$. Two firms produce at zero cost. Each firm receives, for every consumer, a signal of the consumer's group that is correct with probability $\alpha \in (1/2, 1]$, independently across firms. Only consumers of the group a firm targets are interested in its product.
--
--   **Stage 1 (targeting).** Each firm chooses an **action** $(k, m)$: a target group $k \in \{a, b\}$ and a message scope $m$, which is either *expected* (message only the consumers whose signal says they are in group $k$, a mass $1$ of consumers reaching a mass $\alpha$ of group $k$) or *all* (message every consumer, a mass $2$ reaching all of group $k$). The **reach** is $r(\text{expected}) = \alpha$, $r(\text{all}) = 1$, and with a cost $c \ge 0$ per message the **messaging cost** is $c$ and $2c$ respectively. For a stage-1 profile $s = ((k_1, m_1), (k_2, m_2))$:
--   $$
--   S(s) = \begin{cases} r(m_1)\, r(m_2), & k_1 = k_2,\\ 0, & k_1 \neq k_2, \end{cases}\qquad L_i(s) = r(m_i) - S(s).
--   $$
--   $S$ is the mass of shoppers (targeted consumers reached by both firms) and $L_i$ the mass of firm $i$'s loyal consumers.
--
--   **Stage 2 (pricing).** After observing $s$, the firms play the clearinghouse duopoly with valuations $v_i = A$ or $1$ (the value of group $k_i$), loyal masses $L_i(s)$ and shopper mass $S(s)$. $U_i(s; \mu, \nu)$ is firm $i$'s expected profit when firm 1 prices by $\mu$ and firm 2 by $\nu$, and a **pricing equilibrium of subgame $s$** is a mixed Nash equilibrium of that duopoly.
--
--   **SPNE.** A pure targeting profile $s^\star$ together with a continuation $\sigma$, which assigns to every stage-1 profile $s$ a pair of price strategies $\sigma(s) = (\mu_s, \nu_s)$, is a **subgame perfect Nash equilibrium** if $\sigma(s)$ is a pricing equilibrium of subgame $s$ for **every** one of the $16$ profiles $s$, and no firm gains at stage 1 by changing its action, where firm $i$'s stage-1 value of $s$ is $V_i(s) = U_i(s; \sigma(s)) - (\text{its messaging cost})$. The **sum of expected profits** is $V_1(s^\star) + V_2(s^\star)$.
--
--   **Distributions and thresholds.** The cdfs of displays (1) and (2) are
--   $$
--   F(p) = \frac1\alpha - \frac{1-\alpha}{\alpha p}, \qquad H(p) = \frac{p - (1-\alpha)}{p}\quad\text{on } [1-\alpha, 1),
--   $$
--   with both equal to $0$ below $1 - \alpha$ and to $1$ from $1$ on (so $H$ has an atom of mass $1-\alpha$ at $p = 1$). The thresholds are $\hat\alpha_1(A) = 1 - A$ and $\hat\alpha_2(A) = \bigl(1 + \sqrt{1 - 4A}\bigr)/2$.
--
--   **Formalization Note** Targeting is in pure strategies, as in the paper (footnotes 26, 34: randomized targeting equilibria are profit dominated). The message scope is binary (*expected* or *all*), the paper's options (1) and (2); the option of sending no message, relevant only for costly advertising, and the continuous message masses of the Online Appendix's proof are not modelled. Lean's square root is $0$ on negative numbers, so $\hat\alpha_2(A) = 1/2$ when $A > 1/4$, which is the reading the range $(\max\{1/2, \hat\alpha_2(A)\}, 1]$ of Lemma 2 needs.
-- source:
--   Karle & Reisinger, Imperfect Targeting and Advertising Strategies, SSRN 4626076 (March 25, 2024), pp. 7–9 (§3), p. 10 (§4.1, shoppers and loyal consumers), p. 11 (display (1)), p. 14 (definition of α̂₂(A)), p. 15 (display (2)), p. 11 (α̂₁(A) ≡ 1 − A)

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame

open MeasureTheory

namespace ImperfectTargeting.CostlessAds

/-- The two consumer groups: `a` (low valuation `A`) and `b` (high valuation `1`). -/
inductive Group
  | a
  | b
  deriving DecidableEq

/-- Message scope: `expected` messages only the consumers whose signal says they are in the
targeted group; `all` messages every consumer. -/
inductive Scope
  | expected
  | all
  deriving DecidableEq

/-- A stage-1 action: the targeted group and the message scope. -/
abbrev Action := Group × Scope

/-- Valuation of a group: `A` for group `a`, `1` for group `b`. -/
def val (A : ℝ) : Group → ℝ
  | .a => A
  | .b => 1

/-- Mass of targeted-group consumers a firm's messages reach: `α` when it messages its expected
target group, `1` when it messages everyone. -/
def reach (α : ℝ) : Scope → ℝ
  | .expected => α
  | .all => 1

/-- Messaging cost at cost `c` per message: the expected target group has mass `1`, all consumers
have mass `2`. -/
def msgCost (c : ℝ) : Scope → ℝ
  | .expected => c
  | .all => 2 * c

/-- Mass of shoppers (consumers of the targeted group reached by both firms) of the stage-1 profile
`s = (firm 1's action, firm 2's action)`; signals are independent across firms. -/
def shoppers (α : ℝ) (s : Action × Action) : ℝ :=
  if s.1.1 = s.2.1 then reach α s.1.2 * reach α s.2.2 else 0

/-- Mass of firm 1's loyal consumers (targeted consumers reached by firm 1 only). -/
def loyal₁ (α : ℝ) (s : Action × Action) : ℝ := reach α s.1.2 - shoppers α s

/-- Mass of firm 2's loyal consumers (targeted consumers reached by firm 2 only). -/
def loyal₂ (α : ℝ) (s : Action × Action) : ℝ := reach α s.2.2 - shoppers α s

/-- Firm 1's expected stage-2 profit in subgame `s` when firm 1 prices by `μ`, firm 2 by `ν`. -/
noncomputable def U₁ (A α : ℝ) (s : Action × Action) (μ ν : Measure ℝ) : ℝ :=
  expProfit (val A s.1.1) (loyal₁ α s) (shoppers α s) μ ν

/-- Firm 2's expected stage-2 profit in subgame `s` when firm 1 prices by `μ`, firm 2 by `ν`. -/
noncomputable def U₂ (A α : ℝ) (s : Action × Action) (μ ν : Measure ℝ) : ℝ :=
  expProfit (val A s.2.1) (loyal₂ α s) (shoppers α s) ν μ

/-- `(μ, ν)` is a Nash equilibrium in mixed prices of the pricing subgame after stage-1 profile `s`. -/
def IsPricingNE (A α : ℝ) (s : Action × Action) (μ ν : Measure ℝ) : Prop :=
  IsClearinghouseNE (val A s.1.1) (loyal₁ α s) (val A s.2.1) (loyal₂ α s) (shoppers α s) μ ν

/-- Firm 1's stage-1 value of profile `s` under the continuation `cont`: its expected pricing profit
minus its messaging cost. -/
noncomputable def V₁ (A α c : ℝ) (cont : Action × Action → Measure ℝ × Measure ℝ)
    (s : Action × Action) : ℝ :=
  U₁ A α s (cont s).1 (cont s).2 - msgCost c s.1.2

/-- Firm 2's stage-1 value of profile `s` under the continuation `cont`. -/
noncomputable def V₂ (A α c : ℝ) (cont : Action × Action → Measure ℝ × Measure ℝ)
    (s : Action × Action) : ℝ :=
  U₂ A α s (cont s).1 (cont s).2 - msgCost c s.2.2

/-- Subgame perfect Nash equilibrium (pure targeting, mixed pricing): the continuation `cont` is a
pricing Nash equilibrium in every one of the stage-1 subgames, and no firm gains at stage 1 by
deviating from `play` to another action. -/
def IsSPNE (A α c : ℝ) (play : Action × Action)
    (cont : Action × Action → Measure ℝ × Measure ℝ) : Prop :=
  (∀ s : Action × Action, IsPricingNE A α s (cont s).1 (cont s).2) ∧
    (∀ a' : Action, V₁ A α c cont (a', play.2) ≤ V₁ A α c cont play) ∧
    (∀ a' : Action, V₂ A α c cont (play.1, a') ≤ V₂ A α c cont play)

/-- Sum of the two firms' expected profits on the path of play. -/
noncomputable def totalProfit (A α c : ℝ) (play : Action × Action)
    (cont : Action × Action → Measure ℝ × Measure ℝ) : ℝ :=
  V₁ A α c cont play + V₂ A α c cont play

/-- The cdf `F` of display (1): `0` below `1 - α`, `1/α - (1-α)/(α p)` on `[1 - α, 1)`, `1` from `1` on. -/
noncomputable def Fcdf (α p : ℝ) : ℝ :=
  if p < 1 - α then 0 else if p < 1 then 1 / α - (1 - α) / (α * p) else 1

/-- The cdf `H` of display (2): `0` below `1 - α`, `(p - (1-α))/p` on `[1 - α, 1)`, `1` from `1` on
(an atom of mass `1 - α` at `p = 1`). -/
noncomputable def Hcdf (α p : ℝ) : ℝ :=
  if p < 1 - α then 0 else if p < 1 then (p - (1 - α)) / p else 1

/-- The threshold `α̂₁(A) = 1 - A`. -/
def αhat1 (A : ℝ) : ℝ := 1 - A

/-- The threshold `α̂₂(A) = (1 + √(1 - 4A))/2` (Lean's `Real.sqrt` is `0` on negatives, so this is
`1/2` when `A > 1/4`). -/
noncomputable def αhat2 (A : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * A)) / 2

end ImperfectTargeting.CostlessAds


