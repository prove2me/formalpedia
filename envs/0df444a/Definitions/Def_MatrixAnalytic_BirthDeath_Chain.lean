-- Prove2me | Definitions.Def_MatrixAnalytic_BirthDeath_Chain
-- name    : MatrixAnalytic_BirthDeath_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:25.530543+00:00
-- url     : https://prove2.me/theorems/db6abf8a-8519-41e7-9934-3563d9eab6bd
-- title:
--   Markov chains on a countable state space — stochastic matrices, t-step probabilities, aperiodicity, recurrence, positive recurrence, stationary distributions
-- statement:
--   Let $V$ be a countable set of states and $P = (P(x,y))_{x,y\in V}$ a real matrix. The file fixes the notions of Markov chain theory used in Chapter 4, each defined by what it means for the chain, through sums over finite trajectories of products of one-step transition probabilities.
--
--   1. $P$ is **stochastic** if $P(x,y)\ge 0$ for all $x,y$ and every row sums to one, $\sum_y P(x,y) = 1$.
--   2. The **$t$-step transition probabilities** are $P^0(x,y) = \mathbf 1[x=y]$ and $P^{t+1}(x,y) = \sum_z P^t(x,z)P(z,y)$.
--   3. The **period** of a state $x$ is the largest $d$ dividing every $t\ge1$ with $P^t(x,x)>0$; the chain is **aperiodic** if every state has period $1$.
--   4. The **weight** of a trajectory $\omega_0,\dots,\omega_t$ is $\prod_{i<t}P(\omega_i,\omega_{i+1})$.
--   5. For a set $S$, $P_x\{\tau^+_S > t\}$ is the sum of the weights of all trajectories of length $t$ that start at $x$ and avoid $S$ at times $1,\dots,t$; the **return-time tail** is $P_x\{\tau^+_x>t\}$, the case $S=\{x\}$.
--   6. A state $x$ is **recurrent** if $P_x\{\tau^+_x>t\}\to0$ as $t\to\infty$, i.e. the chain returns to $x$ with probability one.
--   7. A state $x$ is **positive recurrent** if $\sum_{t\ge0}P_x\{\tau^+_x>t\}<\infty$, i.e. the expected return time $E_x[\tau^+_x]$ is finite.
--   8. A **stationary distribution** is a vector $\pi$ with $\pi(x)\ge0$, $\sum_x\pi(x)=1$ and $\sum_x\pi(x)P(x,y)=\pi(y)$ for every $y$.
--
--   **Formalization Note** These definitions restate, with the same bodies, the platform's public definition `mm_countable` (namespace `MarkovMixing`, Levin–Peres–Wilmer Ch. 21), which is not available as an importable module in the build environment; they live in the namespace `MatrixAnalytic.BirthDeath`. Recurrence and positive recurrence are the return-time notions, not the existence of a stationary distribution.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 87–88 (Section 4.2; recurrence, positive recurrence, stationary distribution); restates the platform definition mm_countable (Levin, Peres & Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.BirthDeath

/-- A transition function on a countable state space: nonnegative entries, each row summing to
`1`. (Restates `MarkovMixing.IsStochasticC` of the platform definition `mm_countable`.) -/
def IsStochasticC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) : Prop :=
  (∀ x y : V, 0 ≤ P x y) ∧ ∀ x : V, HasSum (P x) 1

/-- The `t`-step transition probabilities `P^t(x,y)`, defined recursively.
(Restates `MarkovMixing.stepPow`.) -/
noncomputable def stepPow {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) :
    ℕ → V → V → ℝ
  | 0 => fun x y => if y = x then 1 else 0
  | t + 1 => fun x y => ∑' z : V, stepPow P t x z * P z y

/-- The period of a state: the largest `d` dividing every `t ≥ 1` with `P^t(x,x) > 0`.
(Restates `MarkovMixing.periodC`.) -/
noncomputable def periodC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (x : V) : ℕ :=
  sSup {d : ℕ | ∀ t : ℕ, 1 ≤ t → 0 < stepPow P t x x → d ∣ t}

/-- Aperiodicity: every state has period `1`. (Restates `MarkovMixing.AperiodicC`.) -/
def AperiodicC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) : Prop :=
  ∀ x : V, periodC P x = 1

/-- The weight `∏ P(ω_i, ω_{i+1})` of a finite trajectory `ω_0, …, ω_t`.
(Restates `MarkovMixing.pathWeightC`.) -/
def pathWeightC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) {t : ℕ}
    (ω : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, P (ω i.castSucc) (ω i.succ)

open Classical in
/-- `P_x{τ⁺_S > t}`: the probability that the chain started at `x` avoids the set `S` at all
times `1, …, t`, as a sum of trajectory weights. (Restates `MarkovMixing.setAvoidTailC`.) -/
noncomputable def setAvoidTailC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (x : V) (S : Set V) (t : ℕ) : ℝ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ S then pathWeightC P ω else 0

/-- `P_x{τ⁺_x > t}`, the tail of the first return time to `x`.
(Restates `MarkovMixing.returnTailC`.) -/
noncomputable def returnTailC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (x : V) (t : ℕ) : ℝ :=
  setAvoidTailC P x {x} t

/-- A state is **recurrent** if `P_x{τ⁺_x < ∞} = 1`, i.e. the return-time tails tend to `0`.
(Restates `MarkovMixing.Recurrent`.) -/
def Recurrent {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)

/-- A state is **positive recurrent** if `E_x(τ⁺_x) < ∞`, i.e. the return-time tails are
summable. (Restates `MarkovMixing.PositiveRecurrent`.) -/
def PositiveRecurrent {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

/-- A stationary distribution: `π ≥ 0`, `∑ π = 1` and `π P = π`.
(Restates `MarkovMixing.IsStationaryC`.) -/
def IsStationaryC {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

end MatrixAnalytic.BirthDeath


