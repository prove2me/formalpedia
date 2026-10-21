-- Prove2me | Definitions.Def_MatrixAnalytic_SkipFree_Chain
-- name    : MatrixAnalytic_SkipFree_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:41.975599+00:00
-- url     : https://prove2.me/theorems/e4f10039-9886-49aa-8aea-1d6eded9f80a
-- title:
--   Markov chains on a countable state space — stochastic matrices, t-step probabilities, irreducibility, positive recurrence, stationary distributions
-- statement:
--   Let $V$ be a countable set of states and $P = (P_{xy})_{x,y\in V}$ a real matrix. The file fixes the notions of Markov chain theory used in Chapter 13, each defined by what it means for the chain, through sums over finite trajectories of products of one-step transition probabilities.
--
--   1. $P$ is **stochastic** if $P_{xy}\ge 0$ for all $x,y$ and every row sums to one, $\sum_y P_{xy} = 1$.
--   2. The **$t$-step transition probabilities** are $P^{(0)}_{xy} = \mathbf 1[x=y]$ and $P^{(t+1)}_{xy} = \sum_z P^{(t)}_{xz}P_{zy}$.
--   3. $P$ is **irreducible** if for all $x,y$ there is $t$ with $P^{(t)}_{xy}>0$.
--   4. The **weight** of a trajectory $\omega_0,\dots,\omega_t$ is $\prod_{i<t}P_{\omega_i\omega_{i+1}}$.
--   5. For a set $A$, $P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories of length $t$ that start at $x$ and avoid $A$ at times $1,\dots,t$; the **return-time tail** is the case $A=\{x\}$.
--   6. A state $x$ is **positive recurrent** if $\sum_{t\ge0}P_x[\tau^+_x>t]<\infty$, i.e. the expected return time to $x$ is finite.
--   7. A **stationary distribution** is a vector $\pi$ with $\pi_x\ge0$, $\sum_x\pi_x=1$ and $\sum_x\pi_xP_{xy}=\pi_y$ for every $y$.
--
--   Chapter 13 works with discrete-time chains only ("To keep the discussion simple, we limit ourselves to discrete time Markov chains", p. 268); the M/G/1- and GI/M/1-type chains and their QBD embeddings are chains on countable state spaces, and their stationary probability vectors are the objects of Corollary 13.1.2 and Theorems 13.1.5 and 13.2.3.
--
--   **Formalization Note** These definitions restate, with the same bodies, the platform's public definition `mm_countable` (namespace `MarkovMixing`), which is not available as an importable module in the build environment; they live in the namespace `MatrixAnalytic.SkipFree`. Positive recurrence is the return-time notion, not the existence of a stationary distribution.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 268 (Chapter 13: discrete-time chains), Section 6.1–6.2 conventions; restates the platform definition mm_countable (Levin, Peres & Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.SkipFree

noncomputable section

/-!
Markov chains on a countable state space, the setting of Chapter 13 of Latouche & Ramaswami
(the M/G/1- and GI/M/1-type chains (13.1), (13.2) live on the countable set
`{(n, i) : n ≥ 0, 1 ≤ i ≤ m}`, their QBD embeddings on `{(n, d, j)}`; "we limit ourselves to
discrete time Markov chains", p. 268). The bodies are those of the platform definition `mm_countable`
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

/-- Irreducibility: every state reaches every other state ("there exists a path between any
two states"). -/
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

/-- A stationary probability vector: `π ≥ 0`, `π1 = 1` and `πP = π`. -/
def IsStationaryC (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

end

end MatrixAnalytic.SkipFree


