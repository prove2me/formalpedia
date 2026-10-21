-- Prove2me | Definitions.Def_MatrixAnalytic_Spectral_Chain
-- name    : MatrixAnalytic_Spectral_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:14.757305+00:00
-- url     : https://prove2.me/theorems/ce7c16e8-59dd-48e3-8147-7a65f4c33233
-- title:
--   Markov chains on a countable state space — stochastic matrix, irreducibility, positive recurrence
-- statement:
--   Chapter 9 studies a quasi-birth-and-death process, a Markov chain on a countable state space. This file fixes the chain-level notions for a matrix $P = (P_{xy})_{x,y \in S}$ with $S$ an arbitrary countable type.
--
--   1. $P$ is **stochastic** if $P_{xy} \ge 0$ for all $x, y$ and every row sums to one, $\sum_{y} P_{xy} = 1$.
--   2. The $t$-step transition probabilities are $P_{xy}(0) = \delta_{xy}$ and $P_{xy}(t+1) = \sum_{z} P_{xz}(t) P_{zy}$; $P$ is **irreducible** if for all $x, y$ there is $t \ge 0$ with $P_{xy}(t) > 0$. The same notion is used for the finite phase matrix $A = A_0 + A_1 + A_2$.
--   3. The weight of a finite trajectory $\omega_0, \dots, \omega_t$ is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$, and $\mathrm P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories starting at $x$ that avoid the set $A$ at times $1, \dots, t$. With $A = \{x\}$ this is the tail of the first return time $\tau^+_x$ to $x$.
--   4. A state $x$ is **positive recurrent** if $\sum_{t \ge 0} \mathrm P_x[\tau^+_x > t] < \infty$, that is, its expected return time is finite; the chain is positive recurrent if every state is.
--
--   **Formalization Note** The bodies are those of the public platform definition `mm_countable` (namespace `MarkovMixing`), restated in the namespace `MatrixAnalytic.Spectral` because that module is not importable in this environment. Positive recurrence is the return-time notion, not the existence of a stationary distribution.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 130 (setting) and p. 204 (standing assumptions of Chapter 9); bodies restated from the platform definition mm_countable (Levin–Peres–Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.Spectral

noncomputable section

/-!
Markov chains on a countable state space, the setting of Chapter 9 of Latouche & Ramaswami
(an irreducible QBD is a chain on the countable set of states `(n, i)`, `n ≥ 0` the level and `i`
the phase). The bodies are those of the platform definition `mm_countable` (namespace
`MarkovMixing`), restated here because that module is not available as an import.
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

/-- Irreducibility: every state reaches every other state. Applied to the QBD (6.1) it is the
irreducibility of the chain; applied to the phase matrix `A = A₀ + A₁ + A₂` it is the
irreducibility of that (finite, stochastic) matrix. -/
def IrreducibleC (P : V → V → ℝ) : Prop :=
  ∀ x y : V, ∃ t : ℕ, 0 < stepPow P t x y

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

/-- The chain is **positive recurrent**: every state is positive recurrent. -/
def IsPositiveRecurrentChain (P : V → V → ℝ) : Prop :=
  ∀ x : V, PositiveRecurrent P x

end

end MatrixAnalytic.Spectral


