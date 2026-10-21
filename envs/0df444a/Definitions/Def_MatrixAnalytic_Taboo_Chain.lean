-- Prove2me | Definitions.Def_MatrixAnalytic_Taboo_Chain
-- name    : MatrixAnalytic_Taboo_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:53.865979+00:00
-- url     : https://prove2.me/theorems/15fb968f-276f-4081-a15a-0530b2696e72
-- title:
--   Markov chains on a countable state space — stochastic matrix, irreducibility, aperiodicity, positive recurrence, stationary vector
-- statement:
--   Chapter 5 works with a Markov chain $\{X_n : n \ge 0\}$ on a denumerable state space $S$ with transition matrix $P$. This file fixes the basic notions, with $S$ an arbitrary countable type.
--
--   1. $P$ is **stochastic** if $P_{xy} \ge 0$ for all $x, y$ and every row sums to one, $\sum_{y} P_{xy} = 1$.
--   2. The $t$-step transition probabilities $P_{xy}(t) = \mathrm P[X_t = y \mid X_0 = x]$ are defined recursively by $P_{xy}(0) = \delta_{xy}$ and $P_{xy}(t+1) = \sum_{z} P_{xz}(t) P_{zy}$.
--   3. The chain is **irreducible** if for all $x, y$ there is $t$ with $P_{xy}(t) > 0$.
--   4. The **period** of $x$ is the largest $d$ dividing every $t \ge 1$ with $P_{xx}(t) > 0$; the chain is **aperiodic** if every state has period $1$.
--   5. The weight of a finite trajectory $\omega_0, \dots, \omega_t$ is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$, and $\mathrm P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories starting at $x$ that avoid the set $A$ at times $1, \dots, t$. With $A = \{x\}$ this is the tail of the first return time to $x$.
--   6. A state $x$ is **positive recurrent** if its expected first return time is finite, i.e. $\sum_{t \ge 0} \mathrm P_x[\tau^+_x > t] < \infty$.
--   7. A **stationary probability vector** is a row vector $\pi$ with $\pi \ge 0$, $\pi\mathbf 1 = 1$ and $\pi P = \pi$, i.e. $\sum_x \pi_x P_{xy} = \pi_y$ for every $y$.
--
--   These are the hypotheses of every statement of the mission: the chapter's standing assumption is an irreducible, aperiodic chain, and Theorem 5.3.1 adds positive recurrence.
--
--   **Formalization Note** The bodies are those of the public platform definition `mm_countable` (namespace `MarkovMixing`, Levin–Peres–Wilmer, Chapter 21), restated in the namespace `MatrixAnalytic.Taboo` because that module is not importable in this environment. Positive recurrence is the return-time notion, never "a stationary distribution exists". Sums of real numbers are Lean's `tsum`/`HasSum`; the trajectory sums are of nonnegative terms.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 107 (setting of Chapter 5); bodies restated from the platform definition mm_countable (Levin–Peres–Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.Taboo

noncomputable section

open scoped BigOperators

/-!
Markov chains on a countable (denumerable) state space, the setting of Chapter 5 of
Latouche & Ramaswami (p. 107): an irreducible, aperiodic chain `{X_n}` on `S` with transition
matrix `P`. The bodies are those of the platform definition `mm_countable`
(namespace `MarkovMixing`), restated here because that module is not available as an import.
-/

variable {V : Type*} [Countable V] [DecidableEq V]

/-- A transition matrix on a countable state space: nonnegative entries, each row summing
to `1`. -/
def IsStochasticC (P : V → V → ℝ) : Prop :=
  (∀ x y : V, 0 ≤ P x y) ∧ ∀ x : V, HasSum (P x) 1

/-- The `t`-step transition probabilities `P_{xy}(t) = P[X_t = y | X_0 = x]`. -/
def stepPow (P : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => fun x y => if y = x then 1 else 0
  | t + 1 => fun x y => ∑' z : V, stepPow P t x z * P z y

/-- Irreducibility: every state reaches every other state. -/
def IrreducibleC (P : V → V → ℝ) : Prop :=
  ∀ x y : V, ∃ t : ℕ, 0 < stepPow P t x y

/-- The period of a state: the gcd of the possible return times. -/
def periodC (P : V → V → ℝ) (x : V) : ℕ :=
  sSup {d : ℕ | ∀ t : ℕ, 1 ≤ t → 0 < stepPow P t x x → d ∣ t}

/-- Aperiodicity: every state has period `1`. -/
def AperiodicC (P : V → V → ℝ) : Prop :=
  ∀ x : V, periodC P x = 1

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a finite trajectory. -/
def pathWeightC (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, P (ω i.castSucc) (ω i.succ)

open Classical in
/-- `P_x[τ⁺_A > t]`: the chain started at `x` avoids the set `A` at all times `1, …, t`. -/
def setAvoidTailC (P : V → V → ℝ) (x : V) (A : Set V) (t : ℕ) : ℝ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A then pathWeightC P ω else 0

/-- `P_x[τ⁺_x > t]`, the tail of the first return time to `x`. -/
def returnTailC (P : V → V → ℝ) (x : V) (t : ℕ) : ℝ :=
  setAvoidTailC P x {x} t

/-- A state is **positive recurrent** if its expected first return time is finite, i.e. the
return-time tails are summable. -/
def PositiveRecurrent (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

/-- A stationary probability vector: `π ≥ 0`, `π1 = 1` and `πP = π`. -/
def IsStationaryC (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

end

end MatrixAnalytic.Taboo


