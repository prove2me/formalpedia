-- Prove2me | Definitions.Def_mm_countable
-- name    : mm_countable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:39:14.098198+00:00
-- url     : https://prove2.me/theorems/412ceda2-32f6-4439-b6f2-8cfe4c53c34e
-- title:
--   Markov chains on countable state spaces
-- statement:
--   This file rebuilds the chain vocabulary on a countable state space, where finite sums become convergent series, following Chapter 21 of Levin–Peres–Wilmer. Everything is stated with explicit summability (`HasSum`/`tsum`); measure theory never enters.
--
--   **Chains on countable spaces.** A transition function $P$ on a countable state space $V$ is **stochastic** when its entries are nonnegative and each row sums to one as an unconditionally convergent series. The $t$-step probabilities are defined recursively, $P^0=I$ and $P^{t+1}(x,y)=\sum_zP^t(x,z)P(z,y)$; the chain is **irreducible** when every state reaches every other at some time, and the **period** of a state is the largest natural number dividing every possible return time (the finite-chain definition of Mission I verbatim), with **aperiodicity** meaning every period is one.
--
--   **Return times, recurrence, and the trichotomy.** Trajectory probabilities over a finite horizon are countable sums of path weights $\prod_{i<t}P(\omega_i,\omega_{i+1})$; in particular the tail $\mathbb P_x\{\tau^+_S>t\}$ of the first return time to a set $S$ is the total weight of length-$t$ trajectories from $x$ avoiding $S$ from time $1$ on. A state is **recurrent** when these tails vanish in the limit, $\mathbb P_x\{\tau^+_x>t\}\to0$ — return is certain — and **positive recurrent** when the tails are moreover summable, which by the tail-sum formula $\mathbb E(\tau)=\sum_{t\ge0}\mathbb P\{\tau>t\}$ says the expected return time $\mathbb E_x(\tau^+_x)$ is finite. Expected return times to sets, $\mathbb E_x(\tau^+_S)$, are defined by the same tail sums (Kac's lemma is a milestone of this mission).
--
--   **Stationarity and distance.** A **stationary distribution** is a nonnegative $\pi$ summing to one with $\sum_x\pi(x)P(x,y)=\pi(y)$ for every $y$, all three conditions as convergent series. The **total variation distance** is taken in its $\ell^1$ form $\tfrac12\sum_y|\mu(y)-\nu(y)|$ (the form that survives the passage to countable spaces; its equivalence with the sup-over-events form is Proposition 4.2 of Mission II in the finite case).
--
--   **Simple random walk on $\mathbb Z^d$.** From $x$, step to one of the $2d$ nearest neighbours $x\pm e_j$ uniformly at random — the chain of Pólya's theorem, this mission's goal.
--
--   **Conventions.** All infinite sums are `tsum`s (non-summable families sum to the junk value $0$) or explicit `HasSum` hypotheses; recurrence and positive recurrence are literally the tail-limit and tail-summability statements above, so no measure-theoretic almost-sure language is needed anywhere.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 21, Sections 21.1-21.3, pp. 275-281

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice

/-!
Markov chains on countable state spaces, following Levin–Peres–Wilmer,
*Markov Chains and Mixing Times*, Chapter 21.

Transition probabilities are functions `P : V → V → ℝ` with rows summing to
one; `t`-step probabilities are defined recursively.  Trajectory
probabilities over a finite horizon are countable sums of path weights, so
recurrence, positive recurrence, and return times are all expressible with
`tsum`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Countable V] [DecidableEq V]

/-- A transition function on a countable state space: nonnegative entries,
each row summing to `1` (LPW Ch. 21). -/
def IsStochasticC (P : V → V → ℝ) : Prop :=
  (∀ x y : V, 0 ≤ P x y) ∧ ∀ x : V, HasSum (P x) 1

/-- The `t`-step transition probabilities `P^t(x,y)` (LPW Ch. 21). -/
def stepPow (P : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => fun x y => if y = x then 1 else 0
  | t + 1 => fun x y => ∑' z : V, stepPow P t x z * P z y

/-- Irreducibility: every state reaches every other (LPW Ch. 21). -/
def IrreducibleC (P : V → V → ℝ) : Prop :=
  ∀ x y : V, ∃ t : ℕ, 0 < stepPow P t x y

/-- The period of a state (gcd of the possible return times), as for finite
chains. -/
def periodC (P : V → V → ℝ) (x : V) : ℕ :=
  sSup {d : ℕ | ∀ t : ℕ, 1 ≤ t → 0 < stepPow P t x x → d ∣ t}

/-- Aperiodicity: every state has period `1`. -/
def AperiodicC (P : V → V → ℝ) : Prop :=
  ∀ x : V, periodC P x = 1

/-- The weight of a finite trajectory. -/
def pathWeightC (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, P (ω i.castSucc) (ω i.succ)

open Classical in
/-- `P_x{τ⁺_S > t}`: the chain started at `x` avoids the set `S` at all
times `1, …, t` (LPW Ch. 21). -/
def setAvoidTailC (P : V → V → ℝ) (x : V) (S : Set V) (t : ℕ) : ℝ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ S then pathWeightC P ω else 0

/-- `P_x{τ⁺_x > t}`, the tail of the first return time (LPW §21.1). -/
def returnTailC (P : V → V → ℝ) (x : V) (t : ℕ) : ℝ :=
  setAvoidTailC P x {x} t

/-- A state is **recurrent** if `P_x{τ⁺_x < ∞} = 1`, i.e. the return-time
tails vanish in the limit (LPW §21.1); otherwise it is transient. -/
def Recurrent (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)

/-- A state is **positive recurrent** if `E_x(τ⁺_x) < ∞`, i.e. the
return-time tails are summable (LPW §21.3). -/
def PositiveRecurrent (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

/-- `E_x(τ⁺_S)`, the expected first return time to the set `S`, via the
tail-sum formula (LPW §21.3, Kac's lemma). -/
def expSetReturnC (P : V → V → ℝ) (x : V) (S : Set V) : ℝ :=
  ∑' t : ℕ, setAvoidTailC P x S t

/-- A stationary distribution on a countable state space:
`π ≥ 0`, `∑ π = 1`, and `π P = π` (LPW §21.3). -/
def IsStationaryC (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

/-- Total variation distance on a countable state space, via the `ℓ¹`
formula of Proposition 4.2. -/
def tvDistC (μ ν : V → ℝ) : ℝ :=
  2⁻¹ * ∑' y : V, |μ y - ν y|

/-- Simple random walk on `ℤ^d`: from `x`, move to one of the `2d`
neighbors `x ± e_j` uniformly at random (LPW §21.2). -/
def srwZ (d : ℕ) : (Fin d → ℤ) → (Fin d → ℤ) → ℝ :=
  fun x y =>
    if ∃ j : Fin d, (∀ i : Fin d, i ≠ j → y i = x i) ∧
        (y j = x j + 1 ∨ y j = x j - 1) then
      ((2 * d : ℕ) : ℝ)⁻¹
    else 0

end

end MarkovMixing


