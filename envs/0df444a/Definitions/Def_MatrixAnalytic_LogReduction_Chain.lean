-- Prove2me | Definitions.Def_MatrixAnalytic_LogReduction_Chain
-- name    : MatrixAnalytic_LogReduction_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:00.47599+00:00
-- url     : https://prove2.me/theorems/ab866e86-03cf-41a5-b5bc-a3ce41132ac5
-- title:
--   Markov chains on a countable state space — stochastic matrices, t-step probabilities, irreducibility, recurrence, positive recurrence
-- statement:
--   Let $V$ be a countable set of states and $P = (P_{xy})_{x,y\in V}$ a real matrix. The file fixes the notions of Markov chain theory used in Chapter 8, each defined by what it means for the chain, through sums over finite trajectories of products of one-step transition probabilities.
--
--   1. $P$ is **stochastic** if $P_{xy}\ge 0$ for all $x,y$ and every row sums to one, $\sum_y P_{xy} = 1$.
--   2. The **$t$-step transition probabilities** are $P^{(0)}_{xy} = \mathbf 1[x=y]$ and $P^{(t+1)}_{xy} = \sum_z P^{(t)}_{xz}P_{zy}$.
--   3. $P$ is **irreducible** if for all $x,y$ there is $t$ with $P^{(t)}_{xy}>0$.
--   4. The **weight** of a trajectory $\omega_0,\dots,\omega_t$ is $\prod_{i<t}P_{\omega_i\omega_{i+1}}$.
--   5. For a set $A$, $P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories of length $t$ that start at $x$ and avoid $A$ at times $1,\dots,t$; the **return-time tail** is the case $A=\{x\}$.
--   6. A state $x$ is **recurrent** if $P_x[\tau^+_x>t]\to0$ as $t\to\infty$, i.e. the chain returns to $x$ with probability one; it is **transient** otherwise.
--   7. A state $x$ is **positive recurrent** if $\sum_{t\ge0}P_x[\tau^+_x>t]<\infty$, i.e. the expected return time to $x$ is finite.
--
--   The QBDs of Chapter 8 are irreducible chains on a countable state space; "ergodic" in the book means positive recurrent (its index: "ergodicity, see positive recurrence").
--
--   **Formalization Note** These definitions restate, with the same bodies, the platform's public definition `mm_countable` (namespace `MarkovMixing`), which is not available as an importable module in the build environment; they live in the namespace `MatrixAnalytic.LogReduction`. Positive recurrence is the return-time notion, not the existence of a stationary distribution.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 165–166 (Chapter 8 opening: the QBD (8.1) is irreducible); restates the platform definition mm_countable (Levin, Peres & Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.LogReduction

noncomputable section

/-!
Markov chains on a countable state space, the setting of Chapter 8 of Latouche & Ramaswami
(a QBD is a chain on the countable set `{(n, i) : n ≥ 0, 1 ≤ i ≤ m}`, with `m ≤ ∞`, p. 165).
The bodies are those of the platform definition `mm_countable` (namespace `MarkovMixing`),
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

/-- A state is **recurrent** if `P_x[τ⁺_x < ∞] = 1`, i.e. the return-time tails tend to `0`.
A state that is not recurrent is **transient**. -/
def Recurrent (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)

/-- A state is **positive recurrent** if its expected first return time is finite, i.e. the
return-time tails are summable. -/
def PositiveRecurrent (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

end

end MatrixAnalytic.LogReduction


