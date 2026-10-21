-- Prove2me | Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
-- name    : MatrixAnalytic_Nonhomogeneous_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:28.834989+00:00
-- url     : https://prove2.me/theorems/ce997959-b74e-40e2-8938-b0bf30817501
-- title:
--   Markov chains on a countable state space — stochastic matrices, t-step probabilities, irreducibility, aperiodicity, recurrence, positive recurrence
-- statement:
--   Let $V$ be a countable set of states and $P = (P_{xy})_{x,y\in V}$ a real matrix. The file fixes the notions of Markov chain theory used in Chapter 12, each defined by what it means for the chain, through sums over finite trajectories of products of one-step transition probabilities.
--
--   1. $P$ is **stochastic** if $P_{xy}\ge 0$ for all $x,y$ and every row sums to one, $\sum_y P_{xy} = 1$.
--   2. The **$t$-step transition probabilities** are $P^{(0)}_{xy} = \mathbf 1[x=y]$ and $P^{(t+1)}_{xy} = \sum_z P^{(t)}_{xz}P_{zy}$.
--   3. $P$ is **irreducible** if for all $x,y$ there is $t$ with $P^{(t)}_{xy}>0$.
--   4. The **period** of a state $x$ is the largest $d$ dividing every $t\ge1$ with $P^{(t)}_{xx}>0$; $P$ is **aperiodic** if every state has period $1$.
--   5. The **weight** of a trajectory $\omega_0,\dots,\omega_t$ is $\prod_{i<t}P_{\omega_i\omega_{i+1}}$.
--   6. For a set $A$, $P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories of length $t$ that start at $x$ and avoid $A$ at times $1,\dots,t$; the **return-time tail** is the case $A=\{x\}$.
--   7. A state $x$ is **recurrent** if $P_x[\tau^+_x>t]\to 0$ as $t\to\infty$, i.e. the chain returns to $x$ with probability one.
--   8. A state $x$ is **positive recurrent** if $\sum_{t\ge0}P_x[\tau^+_x>t]<\infty$, i.e. the expected return time to $x$ is finite.
--
--   "The QBD is recurrent" (respectively positive recurrent) means that every state is.
--
--   **Formalization Note** These definitions restate, with the same bodies, the platform's public definition `mm_countable` (namespace `MarkovMixing`), which is not available as an importable module in the build environment; they live in the namespace `MatrixAnalytic.Nonhomogeneous`. Recurrence and positive recurrence are the return-time notions, not the existence of a stationary distribution.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 259–262 (Chapter 12 setting: an irreducible, aperiodic, recurrent or positive recurrent QBD); restates the platform definition mm_countable (Levin, Peres & Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.Nonhomogeneous

noncomputable section

/-!
Markov chains on a countable state space, the setting of Chapter 12 of Latouche & Ramaswami
(a nonhomogeneous QBD is a chain on the countable set of pairs (level, phase), p. 259). The
bodies are those of the platform definition `mm_countable` (namespace `MarkovMixing`),
restated here because that module is not available as an import.
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

/-- The period of a state (gcd of the possible return times). -/
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

/-- A state is **recurrent** if `P_x[τ⁺_x < ∞] = 1`, i.e. the return-time tails tend to `0`. -/
def Recurrent (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)

/-- A state is **positive recurrent** if its expected first return time is finite, i.e. the
return-time tails are summable. -/
def PositiveRecurrent (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

end

end MatrixAnalytic.Nonhomogeneous


