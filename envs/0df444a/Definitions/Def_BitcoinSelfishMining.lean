-- Prove2me | Definitions.Def_BitcoinSelfishMining
-- name    : BitcoinSelfishMining
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T14:17:01.017548+00:00
-- url     : https://prove2.me/theorems/06ce3c67-b2c4-4fbc-a7b9-35d7f190ef18
-- title:
--   The Eyal–Sirer selfish-mining chain: states, transitions, stationary distribution, revenues and threshold
-- statement:
--   The model of Eyal and Sirer's Section 4, over Mathlib's reals. A pool with hashrate fraction $\alpha$ mines selfishly; of the honest hashrate $1-\alpha$, a fraction $\gamma$ mines on the pool's block during a tie.
--
--   **States.** `State.zero` (no private lead), `State.tie` (the paper's $0'$: a public fork of two equal branches), and `State.lead n`, a private lead of $n+1$ blocks (`lead 0` is the paper's state 1, `lead 1` state 2, `lead (n+2)` state $n+3$). **Outcomes** of a step: `pool` (probability $\alpha$), `honestOnPool` ($(1-\alpha)\gamma$), `honestOnOthers` ($(1-\alpha)(1-\gamma)$); `outcomeProb` and `outcomeSum` name these.
--
--   **`step s o`** is the transition of Figure 1: from `zero` a pool block gives `lead 0`, an honest block stays; from `lead 0` a pool block gives `lead 1`, an honest block gives `tie`; from `tie` every outcome returns to `zero`; from `lead 1` a pool block gives `lead 2`, an honest block returns to `zero`; from `lead (n+2)` a pool block gives `lead (n+3)`, an honest block `lead (n+1)`. **`poolGain`, `othersGain`** are the blocks credited at each transition (equations (8), (9)): at a tie the pool gets 2 for its own block and 1 when honest miners extend its branch, the honest miners get 1 in that case and 2 when they win the tie; honest miners get 1 for a block found in `zero`; the pool gets 2 when an honest block reduces its lead of 2 and 1 when it reduces a lead of at least 3.
--
--   **`P α γ s t`** is the one-step transition probability; **`poolExpGain`, `othersExpGain`** the expected credited blocks from a state. **`stateSum f`** $= f(\text{zero}) + f(\text{tie}) + \sum'_{n} f(\text{lead } n)$, the tail a Mathlib `tsum` (0 if not summable). **`denom α`** $= 2\alpha^3 - 4\alpha^2 + 1$; **`stationary α`** is the paper's distribution (7): $p_0 = (1-2\alpha)/\text{denom}$, $p_{0'} = (1-\alpha)(\alpha - 2\alpha^2)/\text{denom}$, $p_{\text{lead } n} = (\alpha/(1-\alpha))^n (\alpha - 2\alpha^2)/\text{denom}$. **`poolRevenue`, `othersRevenue`** are `stateSum` of $p_s$ times the expected gain; **`relativeRevenue`** $= r_{\text{pool}} / (r_{\text{pool}} + r_{\text{others}})$ (10); **`closedForm α γ`** $= \frac{\alpha(1-\alpha)^2(4\alpha + \gamma(1-2\alpha)) - \alpha^3}{1 - \alpha(1 + (2-\alpha)\alpha)}$; **`profitThreshold γ`** $= (1-\gamma)/(3-2\gamma)$ (11).
--
--   **Formalization Note.** Imports Mathlib. The stationary distribution is the paper's formula taken as a definition; its invariance and total mass are theorems. Real division by zero is 0, so `relativeRevenue` is 0 wherever the revenues sum to 0; the theorems assume $0 < \alpha < 1/2$.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243

import Mathlib

/-!
# Selfish mining (Eyal–Sirer 2014): the state machine, its stationary distribution and revenues

This file states the model of I. Eyal and E. G. Sirer, *Majority is not Enough: Bitcoin Mining is
Vulnerable* (Financial Cryptography 2014; arXiv:1311.0243), Section 4 ("Analysis").

A pool controlling a fraction `α` of the hashrate mines selfishly; the honest miners control `1 - α`.
When the pool publishes a block that ties with an honest block, a fraction `γ` of the honest
hashrate mines on the pool's block, the rest on the honest block.

The *state* is the pool's private lead: `State.zero` (lead 0, no fork), `State.tie` (the paper's
state `0'`: a public fork of two branches of equal height, one headed by the pool's block), and
`State.lead n` which encodes a private lead of **`n + 1`** blocks (so `lead 0` is the paper's
state `1`, `lead 1` is state `2`, `lead (n + 2)` is state `n + 3 ≥ 3`). This shift keeps the state
type free of junk constructors and of proof arguments; the paper's `p_k` for `k ≥ 1` is
`stationary α (State.lead (k - 1))`.

Each step one block is found: by the pool (`Outcome.pool`, probability `α`), by an honest miner
working on the pool's branch (`Outcome.honestOnPool`, probability `(1 - α) γ`), or by an honest
miner working on the honest branch (`Outcome.honestOnOthers`, probability `(1 - α) (1 - γ)`).
Outside the tie state both honest outcomes act alike (there is only one public branch).

The transitions and the number of blocks each side gets credited with are those of Figure 1 and
equations (8)–(9) of the paper, see `step`, `poolGain`, `othersGain`. Sums over the (countable)
state space are written with `stateSum`, which enumerates the states as
`zero, tie, lead 0, lead 1, …` and sums the tail with `tsum`.
-/

namespace BitcoinSelfishMining

/-- The state of the selfish-mining chain: the pool's private lead. `lead n` is a private lead of
`n + 1` blocks (`lead 0` = paper's state 1, `lead 1` = state 2, `lead (n+2)` = state `n+3`);
`tie` is the paper's state `0'`. -/
inductive State
  | zero
  | tie
  | lead (n : ℕ)
  deriving DecidableEq, Repr

/-- Who finds the next block: the pool, an honest miner extending the pool's branch, or an honest
miner extending the honest branch (the last two differ only in the tie state). -/
inductive Outcome
  | pool
  | honestOnPool
  | honestOnOthers
  deriving DecidableEq, Repr

/-- Probability of each outcome of a step: `α`, `(1 - α) γ` and `(1 - α) (1 - γ)`. -/
def outcomeProb (α γ : ℝ) : Outcome → ℝ
  | .pool => α
  | .honestOnPool => (1 - α) * γ
  | .honestOnOthers => (1 - α) * (1 - γ)

/-- Sum of a function over the three outcomes of a step. -/
def outcomeSum (f : Outcome → ℝ) : ℝ :=
  f .pool + f .honestOnPool + f .honestOnOthers

/-- The state transition of the selfish-mining strategy (Figure 1 of the paper):
* from `0`: pool block → lead 1 (kept private); honest block → `0`;
* from `1` (`lead 0`): pool → lead 2; honest → tie `0'` (the pool publishes its block);
* from `0'` (`tie`): every outcome resolves the fork and returns to `0`;
* from `2` (`lead 1`): pool → lead 3; honest → `0` (the pool publishes both blocks);
* from `k ≥ 3` (`lead (n+2)`): pool → lead `k+1`; honest → lead `k-1` (the pool publishes one). -/
def step : State → Outcome → State
  | .zero, .pool => .lead 0
  | .zero, _ => .zero
  | .tie, _ => .zero
  | .lead 0, .pool => .lead 1
  | .lead 0, _ => .tie
  | .lead 1, .pool => .lead 2
  | .lead 1, _ => .zero
  | .lead (n + 2), .pool => .lead (n + 3)
  | .lead (n + 2), _ => .lead (n + 1)

/-- Blocks credited to the pool at a transition (the pool's rewards in the paper's eq. (8)):
2 when it wins the tie, 1 when the honest miners extend its branch at a tie, 2 when its lead of 2
is reduced by an honest block (it publishes both), 1 when a lead `≥ 3` is reduced. -/
def poolGain : State → Outcome → ℕ
  | .tie, .pool => 2
  | .tie, .honestOnPool => 1
  | .tie, .honestOnOthers => 0
  | .lead 1, .pool => 0
  | .lead 1, _ => 2
  | .lead (_ + 2), .pool => 0
  | .lead (_ + 2), _ => 1
  | _, _ => 0

/-- Blocks credited to the honest miners at a transition (eq. (9) of the paper): 1 when they find a
block in state `0`, 1 when they extend the pool's branch at a tie, 2 when they win the tie. -/
def othersGain : State → Outcome → ℕ
  | .zero, .pool => 0
  | .zero, _ => 1
  | .tie, .honestOnPool => 1
  | .tie, .honestOnOthers => 2
  | _, _ => 0

/-- One-step transition probability `P α γ s t` from state `s` to state `t`. -/
noncomputable def P (α γ : ℝ) (s t : State) : ℝ :=
  outcomeSum fun o => if step s o = t then outcomeProb α γ o else 0

/-- Expected number of blocks credited to the pool at a step from state `s`. -/
noncomputable def poolExpGain (α γ : ℝ) (s : State) : ℝ :=
  outcomeSum fun o => outcomeProb α γ o * poolGain s o

/-- Expected number of blocks credited to the honest miners at a step from state `s`. -/
noncomputable def othersExpGain (α γ : ℝ) (s : State) : ℝ :=
  outcomeSum fun o => outcomeProb α γ o * othersGain s o

/-- Sum of a real function over all states: `zero`, `tie`, and the leads `lead 0, lead 1, …`
(the tail is a `tsum`, which is `0` if the family is not summable). -/
noncomputable def stateSum (f : State → ℝ) : ℝ :=
  f .zero + f .tie + ∑' n : ℕ, f (.lead n)

/-- The common denominator `2α³ - 4α² + 1` of the paper's stationary probabilities (eq. (7)). -/
def denom (α : ℝ) : ℝ := 2 * α ^ 3 - 4 * α ^ 2 + 1

/-- The stationary distribution claimed in the paper (eq. (7)):
`p₀ = (1 - 2α) / (2α³ - 4α² + 1)`, `p₀' = (1 - α)(α - 2α²) / (2α³ - 4α² + 1)`,
`p₁ = (α - 2α²) / (2α³ - 4α² + 1)` and `p_k = (α / (1 - α))^(k-1) p₁` for `k ≥ 1`
(recall `lead n` is the lead `k = n + 1`). -/
noncomputable def stationary (α : ℝ) : State → ℝ
  | .zero => (1 - 2 * α) / denom α
  | .tie => (1 - α) * (α - 2 * α ^ 2) / denom α
  | .lead n => (α / (1 - α)) ^ n * ((α - 2 * α ^ 2) / denom α)

/-- The pool's revenue rate (eq. (8)): expected pool blocks per transition in the stationary
regime, `Σ_s p_s · E[pool blocks at a step from s]`. -/
noncomputable def poolRevenue (α γ : ℝ) : ℝ :=
  stateSum fun s => stationary α s * poolExpGain α γ s

/-- The honest miners' revenue rate (eq. (9)). -/
noncomputable def othersRevenue (α γ : ℝ) : ℝ :=
  stateSum fun s => stationary α s * othersExpGain α γ s

/-- The pool's relative revenue `R = r_pool / (r_pool + r_others)` (eq. (10)). -/
noncomputable def relativeRevenue (α γ : ℝ) : ℝ :=
  poolRevenue α γ / (poolRevenue α γ + othersRevenue α γ)

/-- The paper's closed form for the relative revenue (eq. (10)):
`R = (α(1-α)²(4α + γ(1-2α)) - α³) / (1 - α(1 + (2-α)α))`. -/
noncomputable def closedForm (α γ : ℝ) : ℝ :=
  (α * (1 - α) ^ 2 * (4 * α + γ * (1 - 2 * α)) - α ^ 3) / (1 - α * (1 + (2 - α) * α))

/-- The profitability threshold of the paper (eq. (11)): selfish mining beats honest mining iff
`α > (1 - γ) / (3 - 2γ)`. -/
noncomputable def profitThreshold (γ : ℝ) : ℝ := (1 - γ) / (3 - 2 * γ)

end BitcoinSelfishMining


