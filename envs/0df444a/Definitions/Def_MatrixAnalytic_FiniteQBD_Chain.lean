-- Prove2me | Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
-- name    : MatrixAnalytic_FiniteQBD_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:22.000059+00:00
-- url     : https://prove2.me/theorems/32ac0674-a31e-4be3-beff-16f04e5fc018
-- title:
--   Markov chains: stochastic matrix, irreducibility, stationary vector, and the taboo first-entrance probability
-- statement:
--   Chapter 10 works with a discrete-time Markov chain $\{X_n : n \ge 0\}$ on a finite state space with transition matrix $P$. This file fixes the basic notions, stated for an arbitrary countable state space $V$.
--
--   1. $P$ is **stochastic** if $P_{xy} \ge 0$ for all $x, y$ and every row sums to one, $\sum_{y} P_{xy} = 1$.
--   2. The $t$-step transition probabilities are defined recursively by $P_{xy}(0) = \delta_{xy}$ and $P_{xy}(t+1) = \sum_{z} P_{xz}(t) P_{zy}$.
--   3. The chain is **irreducible** if for all $x, y$ there is $t$ with $P_{xy}(t) > 0$.
--   4. The weight of a finite trajectory $\omega_0, \dots, \omega_t$ is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$.
--   5. A **stationary probability vector** is a row vector $\pi$ with $\pi \ge 0$, $\pi\mathbf 1 = 1$ and $\pi P = \pi$.
--   6. For a set $A$ of states, states $x, y$ and $t \ge 0$, the **taboo first-entrance probability**
--   $$f_A(x, y; t+1) = \mathrm P[X_{t+1} = y,\ X_s \notin A \text{ for } 1 \le s \le t \mid X_0 = x]$$
--   is the sum of the weights of the trajectories $x = \omega_0, \omega_1, \dots, \omega_{t+1} = y$ whose intermediate states $\omega_1, \dots, \omega_t$ all lie outside $A$. For $y \in A$ it is the probability that the first visit to $A$ after time $0$ happens at time $t+1$ in the state $y$, so $\sum_{t \ge 0} f_A(x, y; t+1)$ is the probability, starting from $x$, that the first visit to $A$ after time $0$ is a visit to $y$.
--
--   The sum in item 6 over all $t$ is the transition probability from $x$ to $y$ of the process restricted to $A$ (the chain observed only at its visits to $A$, Theorem 5.3.1 of the book), and it is also how the first passage matrices of the chapter are expressed.
--
--   **Formalization Note** Items 1–5 restate the bodies of the public platform definition `mm_countable` (namespace `MarkovMixing`, Levin–Peres–Wilmer, Chapter 21) in the namespace `MatrixAnalytic.FiniteQBD`, because that module is not importable in this environment. Matrices are functions $V \to V \to \mathbb R$, sums are Lean's `tsum`/`HasSum` (finite sums on a finite state space). Item 6 is new; its index $t$ is the number of intermediate states, so the trajectory has $t + 1$ steps.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 221–222 (setting of Chapter 10), p. 118 (restricted process, Theorem 5.3.1); bodies of items 1–5 restated from the platform definition mm_countable (Levin–Peres–Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.FiniteQBD

noncomputable section

/-!
Discrete-time Markov chains, the setting of Chapter 10 of Latouche & Ramaswami (pp. 221–222):
a finite QBD is an irreducible chain on the finite set of states `(n, j)`, `0 ≤ n ≤ M` the level
and `j` the phase. The first five bodies are those of the platform definition `mm_countable`
(namespace `MarkovMixing`), restated here because that module is not available as an import;
they are stated for a countable state space and are applied here to a finite one.
`firstEntryStep` is the taboo first-entrance probability used for the restricted process and
the first passage matrices of the chapter.
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

/-- A stationary probability vector: `π ≥ 0`, `π1 = 1` and `πP = π`. -/
def IsStationaryC (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

open Classical in
/-- Taboo first-entrance probability `P[X_{t+1} = y, X_s ∉ A for 1 ≤ s ≤ t | X_0 = x]`: the sum of
the weights of the trajectories `x = ω₀, ω₁, …, ω_{t+1} = y` whose intermediate states
`ω₁, …, ω_t` all lie outside `A`. For `y ∈ A` it is the probability that the first visit to `A`
after time `0` happens at time `t + 1` and in the state `y`; summed over `t` it is the
probability that the first visit to `A` after time `0` is a visit to `y`. -/
def firstEntryStep (P : V → V → ℝ) (A : Set V) (x y : V) (t : ℕ) : ℝ :=
  ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
        ∀ i : Fin (t + 2), i ≠ 0 → i ≠ Fin.last (t + 1) → ω i ∉ A
    then pathWeightC P ω else 0

end

end MatrixAnalytic.FiniteQBD


