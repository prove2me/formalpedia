-- Prove2me | Definitions.Def_SpacePropTest_ClockAlg
-- name    : SpacePropTest_ClockAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:40.783463+00:00
-- url     : https://prove2.me/theorems/e08bc1e7-d74c-4b43-ab62-088e98313559
-- title:
--   Clock-equipped testers and estimators ($T$ queries, time-dependent transitions, decision at time $T$)
-- statement:
--   A **$T$-query clock-equipped algorithm** with state set $\sigma$ (an $S$-state one when $|\sigma|\le S$) has a start state and, for each time $t<T$ and state $s$, a query distribution $Q_{t,s}$ on $\{0,1\}^n$ and next-state distributions $M_{t,s}(x,b,\cdot)$. On input $f$ it runs exactly $T$ steps: at time $t$ in state $s$ it queries $x\sim Q_{t,s}$ and moves to $s'\sim M_{t,s}(x,f(x),\cdot)$.
--
--   1. A **clock-equipped tester** labels states Acc/Rej and accepts with probability $\Pr[\text{the state at time }T\text{ is Acc}]$.
--   2. A **clock-equipped estimator** outputs $\hat\gamma=\mathrm{est}(s)$ for the state $s$ at time $T$.
--
--   The paper describes its monotonicity algorithm in this model and converts it, with $\log T$ extra bits for the clock, into an $O(ST)$-state tester of Definition 7.
--
--   **Formalization Note** The paper defers the formal definition to its companion [CCP+26]; this is the minimal reading of pp.2–4 and 17 (paper.md decision 6). The clock is not one of the $S$ states.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), §1.2, p.2 (PDF 4); §1.3, p.3 (PDF 5); §5.1, p.17 (PDF 19)

import Mathlib
import Definitions.Def_SpacePropTest_Cube

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

/-- **Clock-equipped algorithms** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio,
*The Space Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…;
§1.2, p.2 (PDF 4), §1.3, p.3, §5.1, p.17 (PDF 19); the formal definition is deferred by the paper
to its companion [CCP+26]).

A `T`-query clock-equipped algorithm with finite state type `σ` (an `S`-state one when
`Fintype.card σ ≤ S`) runs for exactly `T` steps. At step `t < T` in state `s` it queries
`x ∼ Q t s`, receives `f(x)` and moves to `s' ∼ Mt t s x (f x)`. The transitions may depend on the
time `t` (the "clock"), which is not counted among the `S` states.

**Formalization Note.** This is the minimal reading of pp.2–4 and 17 (paper.md decision 6):
time-indexed query and next-state distributions, a start state, and a decision read off the
final state at time `T`. "After `K` queries" means `T ≤ K`. -/
structure ClockAlg (n : ℕ) (σ : Type*) [Fintype σ] where
  /-- The number of queries (time steps). -/
  T : ℕ
  /-- The initial state. -/
  start : σ
  /-- `Q t s x`: probability of querying `x` in state `s` at time `t`. -/
  Q : ℕ → σ → Cube n → ℝ
  /-- `Mt t s x b s'`: probability of entering `s'` at time `t + 1`. -/
  Mt : ℕ → σ → Cube n → Bool → σ → ℝ
  Q_nonneg : ∀ t s x, 0 ≤ Q t s x
  Q_sum : ∀ t s, ∑ x, Q t s x = 1
  Mt_nonneg : ∀ t s x b s', 0 ≤ Mt t s x b s'
  Mt_sum : ∀ t s x b, ∑ s', Mt t s x b s' = 1

namespace ClockAlg

variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The transition matrix at time `t` on input `f`. -/
def step (A : ClockAlg n σ) (f : BoolFn n) (t : ℕ) : Matrix σ σ ℝ :=
  fun s s' => ∑ x, A.Q t s x * A.Mt t s x (f x) s'

/-- The law of the state at time `t` on input `f`. -/
def stateLaw (A : ClockAlg n σ) (f : BoolFn n) : ℕ → σ → ℝ
  | 0 => fun s => if s = A.start then 1 else 0
  | t + 1 => fun s' => ∑ s, stateLaw A f t s * A.step f t s s'

/-- The law of the final state (at time `T`). -/
def finalLaw (A : ClockAlg n σ) (f : BoolFn n) : σ → ℝ := A.stateLaw f A.T

end ClockAlg

/-- A clock-equipped tester: a clock-equipped algorithm whose final state is labelled Acc
(`true`) or Rej (`false`). -/
structure ClockTester (n : ℕ) (σ : Type*) [Fintype σ] extends ClockAlg n σ where
  /-- `acc s = true` iff the final state `s` accepts. -/
  acc : σ → Bool

/-- `Pr[the state at time T is an Acc state]`. -/
def ClockTester.accProb {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ] (A : ClockTester n σ)
    (f : BoolFn n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => A.acc s = true), A.toClockAlg.finalLaw f s

/-- A clock-equipped estimator: a clock-equipped algorithm whose final state `s` outputs the
estimate `γ̂ = est s`. -/
structure ClockEstimator (n : ℕ) (σ : Type*) [Fintype σ] extends ClockAlg n σ where
  /-- The estimate read off the final state. -/
  est : σ → ℝ

/-- `Pr[lo ≤ γ̂ ≤ hi]` for the estimate output at time `T`. -/
def ClockEstimator.probWithin {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : ClockEstimator n σ) (f : BoolFn n) (lo hi : ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => lo ≤ A.est s ∧ A.est s ≤ hi), A.toClockAlg.finalLaw f s

end

end SpacePropTest


