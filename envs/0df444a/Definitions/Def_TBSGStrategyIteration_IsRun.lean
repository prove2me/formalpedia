-- Prove2me | Definitions.Def_TBSGStrategyIteration_IsRun
-- name    : TBSGStrategyIteration_IsRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:33:04.165876+00:00
-- url     : https://prove2.me/theorems/8f07be03-df58-46f1-b7fd-d316237668ef
-- title:
--   Runs of the Strategy-Iteration algorithm (Figure 1, Definition 4.4)
-- statement:
--   Fix a map $\tau_2 : \Pi_1 \to \Pi_2$. A strategy $\sigma \in \Pi_1$ is **greedy** for $v \in \mathbb{R}^n$ (a possible value of the strategy extraction operator $\mathcal P_1 v$, Definition 4.4) if $\sigma(i) \in \arg\min_{a \in A_i} (c + \gamma P v)_a$ for every $i \in S_1$.
--
--   A **run** of Strategy-Iteration$(\sigma^0)$ is a sequence $\sigma^0, \sigma^1, \ldots$ of player 1 strategies with value vectors $v^k = v_{\sigma^k, \tau_2(\sigma^k)}$ such that for every $k$:
--
--   (a) $\sigma^{k+1}$ is greedy for $v^k$ (the step $\sigma^{k+1} \leftarrow \mathcal P_1 v^k$);
--
--   (b) if $\sigma^k$ itself is greedy for $v^k$, then $\sigma^{k+1} = \sigma^k$ (Figure 1's "if possible $\sigma^{k+1} \leftarrow \sigma^k$").
--
--   The algorithm stops at the **termination index** $N$: the first $N \ge 1$ with $\sigma^N = \sigma^{N-1}$, i.e. $\sigma^N = \sigma^{N-1}$ and $\sigma^k \neq \sigma^{k-1}$ for $1 \le k < N$.
--
--   **Formalization Note.** `IsGreedy1`, `runValue` ($v^k$), `IsRun` and `IsTerminationIndex`. The run is an infinite sequence; the algorithm's output sequence is its prefix up to $N$, and by (b) the run is constant from $N-1$ on. Clause (b) is implied by the paper's per-state rule ("ties are broken, if possible, in favor of actions that are in $\sigma^k$"), so results stated for runs cover that reading too. $\tau_2$ is a parameter; the theorems assume that $\tau_2(\sigma)$ is an optimal counter-strategy against $\sigma$ for every $\sigma$.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 8, Figure 1 and §5 text; p. 7, Definition 4.4

import Mathlib
import Definitions.Def_TBSGStrategyIteration_value
import Definitions.Def_TBSGStrategyIteration_valueIterOp

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- `σ` is a possible value of the strategy extraction operator `𝒫₁ v` (Def. 4.4):
for every `i ∈ S₁`, `σ(i) ∈ A_i` attains `min_{A_i} (c + γPv)`. -/
def IsGreedy1 (G : Game S A) (v : S → ℝ) (σ : Strat1 G) : Prop :=
  ∀ i : {i : S // i ∈ G.S1}, ∀ a : A, G.src a = i → qValue G v (σ.act i) ≤ qValue G v a

/-- The `k`-th value vector `v^k = v_{σ^k, τ₂(σ^k)}` of a Strategy-Iteration run `σ` with
counter-strategy map `τ₂` (Figure 1). -/
noncomputable def runValue (G : Game S A) (τ₂ : Strat1 G → Strat2 G) (σ : ℕ → Strat1 G)
    (k : ℕ) : S → ℝ :=
  value G (σ k, τ₂ (σ k))

/-- A run of Strategy-Iteration(σ⁰) (Figure 1, p. 8) with counter-strategy map `τ₂`, as an
infinite sequence `σ⁰, σ¹, …` of player 1 strategies: for every `k`,
(a) `σ^{k+1} = 𝒫₁ v^k`, i.e. `σ^{k+1}` is greedy for `v^k = v_{σ^k, τ₂(σ^k)}`, and
(b) "if possible `σ^{k+1} ← σ^k`": if `σ^k` itself is greedy for `v^k`, then `σ^{k+1} = σ^k`. -/
def IsRun (G : Game S A) (τ₂ : Strat1 G → Strat2 G) (σ : ℕ → Strat1 G) : Prop :=
  ∀ k : ℕ, IsGreedy1 G (runValue G τ₂ σ k) (σ (k + 1)) ∧
    (IsGreedy1 G (runValue G τ₂ σ k) (σ k) → σ (k + 1) = σ k)

/-- `N` is the iteration at which the run stops (`until σ^{k−1} = σ^k`, Figure 1):
`N ≥ 1`, `σ^N = σ^{N−1}`, and `σ^k ≠ σ^{k−1}` for every `1 ≤ k < N`. -/
def IsTerminationIndex {G : Game S A} (σ : ℕ → Strat1 G) (N : ℕ) : Prop :=
  1 ≤ N ∧ σ N = σ (N - 1) ∧ ∀ k : ℕ, 1 ≤ k → k < N → σ k ≠ σ (k - 1)

end TBSGStrategyIteration


