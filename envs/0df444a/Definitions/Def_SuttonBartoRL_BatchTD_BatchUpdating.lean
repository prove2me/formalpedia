-- Prove2me | Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating
-- name    : SuttonBartoRL_BatchTD_BatchUpdating
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:37:29.292063+00:00
-- url     : https://prove2.me/theorems/b3086b60-c18c-470b-a392-f971ac011be6
-- title:
--   Batch-updating TD(0) and constant-$\alpha$ MC, and the certainty-equivalence estimate
-- statement:
--   A **batch** is a finite list of observed episodes over a finite set $\mathcal S$ of nonterminal states. A **visit** of $s \in \mathcal S$ is a pair (episode, time $t < T$) with $S_t = s$; every visit is counted, and $n(s)$ is the number of visits of $s$.
--
--   **Batch updating.** Given an array $V$, the increments of TD(0) (6.2) are computed for every visit and summed, and $V$ is changed only once by $\alpha$ times the sum:
--
--   $$
--   V_{m+1}(s) = V_m(s) + \alpha \sum_{\text{visits } t \text{ of } s} \big[R_{t+1} + \gamma V_m(S_{t+1}) - V_m(S_t)\big],
--   $$
--
--   with $V_m(\text{terminal}) = 0$. **Batch constant-$\alpha$ MC** is the same iteration with the increment $G_t - V_m(S_t)$ of (6.1). The **sample average** of the returns after $s$ is $\bar G(s) = n(s)^{-1}\sum_{\text{visits of } s} G_t$, and the **squared error** of an array $V$ on the training set is $\sum_{\text{episodes}}\sum_{t<T}(G_t - V(S_t))^2$.
--
--   **Maximum-likelihood model.** For $i \in \mathcal S$ visited and $j \in \mathcal S^+$, let $N(i, j)$ be the number of observed transitions from $i$ to $j$. The estimated transition probability is $\hat p(j \mid i) = N(i, j)/n(i)$, and the associated expected reward $\hat r(i, j)$ is the average of the rewards observed on those transitions. The expected one-step reward is $\hat r(i) = \sum_{j \in \mathcal S^+}\hat p(j\mid i)\,\hat r(i,j)$, and $\hat P$ is the matrix $(\hat p(s' \mid s))_{s, s' \in \mathcal S}$ on nonterminal states. The **certainty-equivalence estimate** is the value function of this Markov reward process, with the terminal state absorbing and rewarding $0$:
--
--   $$
--   \hat v(s) = \mathbb E\Big[\sum_{k \ge 0}\gamma^k R_{k+1} \,\Big|\, S_0 = s\Big] = \sum_{k \ge 0} \gamma^k \big(\hat P^k \hat r\big)(s).
--   $$
--
--   These are the objects compared in the section on the optimality of TD(0): batch TD(0) and batch MC, and the two answers they converge to.
--
--   **Formalization Note** The sums over visits are over every episode of the list and every $t < T$ with $S_t = s$. For an unvisited state, $n(s) = 0$ and the real divisions defining $\hat p$, $\hat r$ and $\bar G(s)$ return $0$; such a state has no increment, so both batch iterations leave its value unchanged, and the theorems treat it separately. The estimate $\hat v$ is defined from returns (the series), not as the solution of a Bellman equation; its convergence at $\gamma = 1$ is part of the theorems that use it, not assumed.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §6.3 batch updating, p. 126; sample averages, p. 127; maximum-likelihood model and certainty-equivalence estimate, p. 128

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes

namespace SuttonBartoRL.BatchTD

/-- A batch of training data (§6.3, p. 126): a finite list of observed episodes, each ending in the
terminal state. -/
abbrev Batch (S : Type) := List (Episode S)

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Sum of `f e t` over every visit of the nonterminal state `s` in the batch, i.e. over every
episode `e` of the batch and every time `t < T_e` with `S_t = s` (every-visit counting; a state
visited several times in one episode contributes once per visit). -/
noncomputable def visitSum (b : Batch S) (s : S) (f : Episode S → ℕ → ℝ) : ℝ :=
  (b.map fun e =>
    ∑ t ∈ Finset.range e.length, if stateAt e t = some s then f e t else 0).sum

/-- The number `n(s)` of visits to the nonterminal state `s` in the batch (every visit counted). -/
def visitCount (b : Batch S) (s : S) : ℕ :=
  (b.map fun e => ((Finset.range e.length).filter fun t => stateAt e t = some s).card).sum

/-- The batch TD(0) increment at `s`: the sum, over every visit `t` of `s` in the batch, of the
TD(0) increment `R_{t+1} + γ V(S_{t+1}) − V(S_t)` of (6.2)/(6.5), all computed with the same `V`. -/
noncomputable def tdIncrement (γ : ℝ) (b : Batch S) (V : S → ℝ) (s : S) : ℝ :=
  visitSum b s (tdError γ V)

/-- One batch update of TD(0) (§6.3, p. 126): the value function is changed only once, by `α`
times the sum of all the increments. States never visited are left unchanged. -/
noncomputable def batchTDStep (α γ : ℝ) (b : Batch S) (V : S → ℝ) : S → ℝ :=
  fun s => V s + α * tdIncrement γ b V s

/-- The iterates `V_0, V_1, V_2, …` of batch-updating TD(0) from the initial array `V₀`:
`V_{m+1} = V_m + α Σ_{visits} [R_{t+1} + γ V_m(S_{t+1}) − V_m(S_t)]`. -/
noncomputable def batchTD (α γ : ℝ) (b : Batch S) (V₀ : S → ℝ) (m : ℕ) : S → ℝ :=
  (batchTDStep α γ b)^[m] V₀

/-- The batch constant-α MC increment at `s`: the sum, over every visit `t` of `s`, of the
increment `G_t − V(S_t)` of (6.1). -/
noncomputable def mcIncrement (γ : ℝ) (b : Batch S) (V : S → ℝ) (s : S) : ℝ :=
  visitSum b s (fun e t => ret γ e t - extV V (stateAt e t))

/-- One batch update of constant-α MC (6.1) (§6.3, p. 126). -/
noncomputable def batchMCStep (α γ : ℝ) (b : Batch S) (V : S → ℝ) : S → ℝ :=
  fun s => V s + α * mcIncrement γ b V s

/-- The iterates of batch-updating constant-α MC from `V₀`. -/
noncomputable def batchMC (α γ : ℝ) (b : Batch S) (V₀ : S → ℝ) (m : ℕ) : S → ℝ :=
  (batchMCStep α γ b)^[m] V₀

/-- The sample average of the returns observed after the visits to `s` (every visit):
`(Σ_{visits of s} G_t) / n(s)`. Only meaningful for visited `s` (it is `0` when `n(s) = 0`). -/
noncomputable def mcAverage (γ : ℝ) (b : Batch S) (s : S) : ℝ :=
  visitSum b s (fun e t => ret γ e t) / (visitCount b s : ℝ)

/-- The squared error `Σ_{episodes} Σ_{t < T} (G_t − V(S_t))²` of an estimate `V` on the training
set (the "mean square error from the actual returns in the training set", p. 127, up to the
constant factor `1 / (number of visits)`). -/
noncomputable def mcSquaredError (γ : ℝ) (b : Batch S) (V : S → ℝ) : ℝ :=
  (b.map fun e =>
    ∑ t ∈ Finset.range e.length, (ret γ e t - extV V (stateAt e t)) ^ 2).sum

/-- The number of observed transitions from the nonterminal state `s` to `j ∈ S⁺ = Option S`
(`j = none` is the terminal state). -/
def transCount (b : Batch S) (s : S) (j : Option S) : ℕ :=
  (b.map fun e => ((Finset.range e.length).filter fun t =>
    stateAt e t = some s ∧ stateAt e (t + 1) = j).card).sum

/-- The sum of the rewards observed on the transitions from `s` to `j`. -/
noncomputable def transRewardSum (b : Batch S) (s : S) (j : Option S) : ℝ :=
  visitSum b s (fun e t => if stateAt e (t + 1) = j then nextReward e t else 0)

/-- Maximum-likelihood transition probability (p. 128): the fraction of observed transitions from
`s` that went to `j`. It is `0` for an unvisited `s` (real division by zero). -/
noncomputable def mlProb (b : Batch S) (s : S) (j : Option S) : ℝ :=
  (transCount b s j : ℝ) / (visitCount b s : ℝ)

/-- Maximum-likelihood expected reward of the transition `s → j` (p. 128): the average of the
rewards observed on those transitions (`0` if there were none). -/
noncomputable def mlReward (b : Batch S) (s : S) (j : Option S) : ℝ :=
  transRewardSum b s j / (transCount b s j : ℝ)

/-- Expected one-step reward from `s` in the maximum-likelihood Markov reward process:
`r̂(s) = Σ_{j ∈ S⁺} p̂(j | s) r̂(s, j)`. -/
noncomputable def mlExpectedReward (b : Batch S) (s : S) : ℝ :=
  ∑ j : Option S, mlProb b s j * mlReward b s j

/-- The maximum-likelihood transition matrix restricted to nonterminal states,
`P̂ s s' = p̂(s' | s)`; the missing mass of each visited row is the probability of termination. -/
noncomputable def mlMatrix (b : Batch S) : Matrix S S ℝ :=
  fun s s' => mlProb b s (some s')

/-- The **certainty-equivalence estimate** (p. 128): the value function of the maximum-likelihood
Markov reward process, defined from returns as
`v̂(s) = E[Σ_{k≥0} γ^k R_{k+1} | S_0 = s] = Σ_{k≥0} γ^k (P̂^k r̂)(s)`, the terminal state being
absorbing with reward `0`. -/
noncomputable def ceEstimate (γ : ℝ) (b : Batch S) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s

end SuttonBartoRL.BatchTD


