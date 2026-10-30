-- Prove2me | Definitions.Def_BitcoinSelfishErgodic
-- name    : BitcoinSelfishErgodic
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T23:27:12.705108+00:00
-- url     : https://prove2.me/theorems/1047a24f-5b86-46ea-adea-ef5cb7135032
-- title:
--   Distributions of the selfish-mining chain over time, Cesàro averages, and time-averaged revenues
-- statement:
--   Names over the selfish-mining missions' chain (`State`, `P`, `stateSum`, `poolExpGain`, `othersExpGain`).
--
--   **`delta t`** — the point mass at state $t$. **`dist α γ μ`** — one step of the chain on a distribution: $(\mathrm{dist}\,\mu)(s) = \sum_t \mu(t)\, P(t, s)$ through `stateSum`. **`distN α γ μ n`** — $n$ steps. **`IsDist μ`** — nonnegative, summable on the leads, total mass 1. **`cesaro α γ μ n`** — the average $\frac1n \sum_{k<n} \mathrm{distN}\,\mu\,k$ (the expected fraction of the first $n$ times spent in each state).
--
--   **`expPoolGain α γ μ`**, **`expOthersGain α γ μ`** — expected blocks credited per step when the state has distribution $\mu$. **`avgPoolGain α γ n`**, **`avgOthersGain α γ n`** — expected blocks per step over the first $n$ steps from `zero`; **`avgRelativeRevenue α γ n`** — their ratio, the pool's time-averaged revenue share (real division, 0 when the denominator is 0).
--
--   **`kill μ`** — the distribution with the mass at `zero` removed. **`taboo α γ t n`** — the sub-distribution of the chain from $t$ killed on hitting `zero` at times $\ge 1$. **`firstPassage α γ t n`** — the probability of first hitting `zero` at time $n+1$ from $t$. **`returnProb α γ n`** — $P(X_n = \text{zero} \mid X_0 = \text{zero})$. **`noPassage α γ t n`** — the probability of not having hit `zero` by time $n$.
--
--   **Formalization Note.** Imports Mathlib and the two selfish-mining missions' definitions. Real division by zero is 0.
-- source:
--   I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 (the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique (uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)

import Definitions.Def_BitcoinSelfishMining
import Definitions.Def_BitcoinSelfishUnique

/-!
# Selfish mining: the chain started at a state, its `n`-step distributions, Cesàro averages and
time-averaged revenues

This file sets up the dynamics of the Eyal–Sirer selfish-mining chain of
`Definitions/Def_BitcoinSelfishMining.lean` (states `zero | tie | lead n`, one-step transition
probabilities `P α γ s t`, sums over the countable state space `stateSum`) as an evolution of
distributions on the state space, so that the ergodic statements can be formulated:

* `delta t` is the point mass at the state `t`, `dist α γ μ` is the distribution after one step
  of the chain started with distribution `μ` (`(dist μ) s = Σ_t μ t · P(t → s)`), and
  `distN α γ μ n` the distribution after `n` steps.
* `IsDist μ` says that `μ` is a probability distribution on the states (nonnegative, summable on
  the leads, total mass one). `BitcoinSelfishUnique.IsStationary α γ μ` is `IsDist μ` plus
  invariance under `dist`.
* `cesaro α γ μ n` is the Cesàro average `(1/n) Σ_{k<n} distN α γ μ k` of the first `n`
  distributions of the chain started at `μ`.
* `expPoolGain α γ μ` and `expOthersGain α γ μ` are the expected numbers of blocks credited to the
  pool / to the honest miners at one step of the chain whose current state has distribution
  `μ` (so `poolRevenue α γ = expPoolGain α γ (stationary α)` by definition).
* `avgPoolGain α γ n` and `avgOthersGain α γ n` are the expected numbers of blocks per step
  credited to the pool / to the honest miners, averaged over the first `n` steps of the chain
  started at `zero`, and `avgRelativeRevenue α γ n` is the corresponding time-averaged relative
  revenue of the pool. The theorems of `Solutions/Sol_BitcoinSelfishErgodic_all.lean` show that
  these converge to the paper's stationary quantities `poolRevenue`, `othersRevenue` and
  `relativeRevenue`, which makes the paper's revenue analysis a statement about long-run averages.
* `taboo α γ t n` is the sub-distribution of the chain started at `t` and killed when it hits
  `zero`, `firstPassage α γ t n` the probability that this first hit happens at time `n + 1`,
  `noPassage α γ t n` the probability of no hit up to time `n`, and `returnProb α γ n` the
  renewal sequence `P(X_n = zero | X_0 = zero)`. They are used to prove the convergence of the
  `n`-step distributions themselves (not only of their Cesàro averages) to `stationary α`.
-/

namespace BitcoinSelfishErgodic

open BitcoinSelfishMining

/-- The state space is countable (`zero ↦ 0`, `tie ↦ 1`, `lead n ↦ n + 2`). -/
instance : Countable State :=
  Function.Injective.countable (f := fun s : State => match s with
    | .zero => 0
    | .tie => 1
    | .lead n => n + 2) (by
    intro s t h
    cases s <;> cases t <;> simp_all)

/-- The point mass at the state `t`. -/
noncomputable def delta (t : State) : State → ℝ := fun s => if s = t then 1 else 0

/-- One step of the chain acting on distributions: `(dist α γ μ) s = Σ_t μ t · P α γ t s`. -/
noncomputable def dist (α γ : ℝ) (μ : State → ℝ) : State → ℝ :=
  fun s => stateSum (fun t => μ t * P α γ t s)

/-- The distribution of the chain after `n` steps, started with distribution `μ`. -/
noncomputable def distN (α γ : ℝ) (μ : State → ℝ) : ℕ → State → ℝ
  | 0 => μ
  | n + 1 => dist α γ (distN α γ μ n)

/-- A probability distribution on the states: nonnegative, summable on the leads (so that
`stateSum μ` is a genuine sum), of total mass one. -/
structure IsDist (μ : State → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ μ s
  summable : Summable (fun n : ℕ => μ (.lead n))
  mass : stateSum μ = 1

/-- The Cesàro average `(1/n) Σ_{k<n} distN α γ μ k` of the first `n` distributions of the chain
started at `μ` (the expected fraction of the times `0, …, n-1` spent in each state). -/
noncomputable def cesaro (α γ : ℝ) (μ : State → ℝ) (n : ℕ) : State → ℝ :=
  fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s

/-- Expected number of blocks credited to the pool at one step of the chain, when the current
state has distribution `μ`: `Σ_s μ s · poolExpGain α γ s`. -/
noncomputable def expPoolGain (α γ : ℝ) (μ : State → ℝ) : ℝ :=
  stateSum (fun s => μ s * poolExpGain α γ s)

/-- Expected number of blocks credited to the honest miners at one step of the chain, when the
current state has distribution `μ`. -/
noncomputable def expOthersGain (α γ : ℝ) (μ : State → ℝ) : ℝ :=
  stateSum (fun s => μ s * othersExpGain α γ s)

/-- The expected number of blocks per step credited to the pool over the first `n` steps of the
chain started at `zero`: `(1/n) Σ_{k<n} Σ_s P(X_k = s) · poolExpGain α γ s`. -/
noncomputable def avgPoolGain (α γ : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
    stateSum (fun s => distN α γ (delta .zero) k s * poolExpGain α γ s)

/-- The expected number of blocks per step credited to the honest miners over the first `n` steps
of the chain started at `zero`. -/
noncomputable def avgOthersGain (α γ : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
    stateSum (fun s => distN α γ (delta .zero) k s * othersExpGain α γ s)

/-- The pool's time-averaged relative revenue over the first `n` steps of the chain started at
`zero`: expected pool blocks divided by expected total blocks. -/
noncomputable def avgRelativeRevenue (α γ : ℝ) (n : ℕ) : ℝ :=
  avgPoolGain α γ n / (avgPoolGain α γ n + avgOthersGain α γ n)

/-- Killing at `zero`: the mass at `zero` is removed, every other state is kept. -/
noncomputable def kill (μ : State → ℝ) : State → ℝ := fun s => if s = .zero then 0 else μ s

/-- The taboo sub-distributions of the chain started at `t` and killed when it hits `zero` (at a
time `≥ 1`): `taboo α γ t n s = P(X_n = s, X_1 ≠ zero, …, X_n ≠ zero | X_0 = t)`. -/
noncomputable def taboo (α γ : ℝ) (t : State) : ℕ → State → ℝ
  | 0 => delta t
  | n + 1 => kill (dist α γ (taboo α γ t n))

/-- `firstPassage α γ t n` is the probability that the chain started at `t` hits `zero` for the
first time (among the times `≥ 1`) at time `n + 1`. For `t = zero` this is the distribution of
the first return time to `zero`. -/
noncomputable def firstPassage (α γ : ℝ) (t : State) (n : ℕ) : ℝ :=
  dist α γ (taboo α γ t n) .zero

/-- The renewal sequence of the state `zero`: `returnProb α γ n = P(X_n = zero | X_0 = zero)`. -/
noncomputable def returnProb (α γ : ℝ) (n : ℕ) : ℝ := distN α γ (delta .zero) n .zero

/-- `noPassage α γ t n` is the probability that the chain started at `t` has not hit `zero` at
any of the times `1, …, n` (the total mass of `taboo α γ t n`). -/
noncomputable def noPassage (α γ : ℝ) (t : State) (n : ℕ) : ℝ := stateSum (taboo α γ t n)

end BitcoinSelfishErgodic


