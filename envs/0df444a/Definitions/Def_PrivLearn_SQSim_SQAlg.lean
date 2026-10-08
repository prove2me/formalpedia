-- Prove2me | Definitions.Def_PrivLearn_SQSim_SQAlg
-- name    : PrivLearn_SQSim_SQAlg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:14.327985+00:00
-- url     : https://prove2.me/theorems/127bff02-2c91-4a30-80e2-70f6c5099a73
-- title:
--   Statistical query algorithms with a random number of queries (Definition 5.5), SQ oracles, output law and expected query count
-- statement:
--   A **statistical query (SQ) algorithm** $B$ (Definition 5.5) accesses a distribution $P$ on $D$ only through an SQ oracle. Here $B$ is a randomized state machine on a set $\Sigma$ of states: it starts in a random state; in each state $s$ it either stops with an output $o$, or it asks the oracle a query $(g,\tau)$, with $g:D\to\mathbb R$ and tolerance $\tau$, receives an answer $v$, and moves to a random next state whose law depends on $s$ and $v$. The number of queries is random and unbounded.
--
--   1. $B$ **asks only legal queries of tolerance $\tau$** if every query it can ask has tolerance exactly $\tau$ and a measurable query function with values in $[-1,1]$.
--   2. An **SQ oracle** answers each query as an arbitrary function of the whole sequence of states visited so far. It is **valid for $P$** if every answer $v$ to a query $(g,\tau)$ satisfies $|v-\mathbb E_{u\sim P}[g(u)]|\le\tau$ (Definition 5.4).
--   3. Running $B$ against an oracle $O$ gives a Markov chain on configurations. The **output law** $\Pr[B\text{ outputs }o]$ is the probability that $B$ eventually stops with output $o$; it is a sub-probability mass function, its missing mass being the probability that $B$ never stops.
--   4. The **expected number of queries** is
--
--   $$\mathbb E[\#\text{queries}]=\sum_{N\ge0}\Pr[\text{at step }N,\ B\text{ asks a query}]\in[0,\infty],$$
--
--   which counts every query and is infinite whenever $B$ fails to stop with positive probability.
--
--   These are the SQ algorithms of Lemma 5.8, which bounds the expected query count and the statistical difference of the output law against every valid oracle.
--
--   **Formalization Note.** The oracle is deterministic and may depend on the full state trajectory (which determines every earlier query and answer); a randomized oracle is a mixture of such oracles. Validity is required at every trajectory, reachable or not. Without the restriction to $[-1,1]$-valued queries the tolerance would be meaningless, because scaling $g$ by $M$ divides the effective tolerance by $M$. The algorithm sees the distribution only through answers: $P$ does not appear in its definition.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 19 (Definitions 5.4, 5.5), p. 21 (Lemma 5.8), p. 22 (algorithm B_{R,ε})

import Mathlib
import Definitions.Def_PrivLearn_SQSim_Privacy

namespace PrivLearn.SQSim

open MeasureTheory

/-- Definition 5.5 (p. 19): a (possibly adaptive) statistical query algorithm with a random,
unbounded number of queries, as a state machine on a state type `σ`. It starts in a random state
drawn from `start`. In state `s` it either stops and outputs `o` (`step s = .inl o`), or it asks
the SQ oracle the query `(g, τ)` and moves to a random next state drawn from `k v`, where `v` is
the oracle's answer (`step s = .inr (g, τ, k)`). Its coins are inside `start` and `k`; it sees the
distribution only through the answers `v`. -/
structure SQAlg (Dom Out σ : Type*) where
  start : PMF σ
  step : σ → Out ⊕ ((Dom → ℝ) × ℝ × (ℝ → PMF σ))

namespace SQAlg

variable {Dom Out σ : Type*}

/-- `B` asks only legal queries of tolerance `τ`: every query `(g, τ')` it can ask has `τ' = τ`
and a measurable query function `g : Dom → [−1, 1]`. -/
def AsksOnly [MeasurableSpace Dom] (B : SQAlg Dom Out σ) (τ : ℝ) : Prop :=
  ∀ (s : σ) (g : Dom → ℝ) (τ' : ℝ) (k : ℝ → PMF σ), B.step s = .inr (g, τ', k) →
    τ' = τ ∧ Measurable g ∧ ∀ u, |g u| ≤ 1

/-- An SQ oracle for `B` is a rule `O` that answers the query asked in the current state, as a
function of the whole trajectory of states so far (newest first; the current state is the head).
It is valid for the distribution `P` (Definition 5.4) if every answer `v` to a query `(g, τ)`
satisfies `|v − E_{u∼P}[g(u)]| ≤ τ`. -/
def IsValidOracle [MeasurableSpace Dom] (B : SQAlg Dom Out σ) (P : Measure Dom)
    (O : List σ → ℝ) : Prop :=
  ∀ (s : σ) (h : List σ) (g : Dom → ℝ) (τ : ℝ) (k : ℝ → PMF σ),
    B.step s = .inr (g, τ, k) → IsSQAnswer P g τ (O (s :: h))

/-- One step of `B` run against the oracle `O`. A configuration is either `.inl o` (stopped with
output `o`) or `.inr traj` (running, `traj` the states visited so far, newest first; `[]` before
the start). -/
noncomputable def next (B : SQAlg Dom Out σ) (O : List σ → ℝ) :
    Out ⊕ List σ → PMF (Out ⊕ List σ)
  | .inl o => PMF.pure (.inl o)
  | .inr [] => B.start.map fun s => .inr [s]
  | .inr (s :: h) =>
    match B.step s with
    | .inl o => PMF.pure (.inl o)
    | .inr (_, _, k) => (k (O (s :: h))).map fun s' => .inr (s' :: s :: h)

/-- The law of the configuration after `N` steps of `B` against `O`. -/
noncomputable def run (B : SQAlg Dom Out σ) (O : List σ → ℝ) : ℕ → PMF (Out ⊕ List σ)
  | 0 => PMF.pure (.inr [])
  | N + 1 => (B.run O N).bind (B.next O)

/-- The output distribution of `B` against `O`: `Pr[B stops and outputs o]`. It is a
sub-probability mass function; the missing mass is the probability that `B` never stops. -/
noncomputable def outputLaw (B : SQAlg Dom Out σ) (O : List σ → ℝ) (o : Out) : ENNReal :=
  ⨆ N : ℕ, B.run O N (.inl o)

/-- A configuration in which `B` is about to ask a query. -/
def Querying (B : SQAlg Dom Out σ) : Out ⊕ List σ → Prop
  | .inr (s :: _) => (B.step s).isRight = true
  | _ => False

/-- The expected number of SQ queries `B` makes against `O`, counting every query (in `[0, ∞]`):
`Σ_N Pr[at time N, B asks a query]`. -/
noncomputable def expectedQueries (B : SQAlg Dom Out σ) (O : List σ → ℝ) : ENNReal :=
  ∑' N : ℕ, (B.run O N).toOuterMeasure {c | B.Querying c}

end SQAlg

end PrivLearn.SQSim


