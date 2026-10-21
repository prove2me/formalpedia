-- Prove2me | Definitions.Def_MatrixAnalytic_Stability_Chain
-- name    : MatrixAnalytic_Stability_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:00.022392+00:00
-- url     : https://prove2.me/theorems/07a511ad-ac3f-4099-8a61-9937d32fbd07
-- title:
--   Markov chains on a countable state space — stochastic matrix, irreducibility, recurrence, positive recurrence, null recurrence, transience
-- statement:
--   Chapter 7 classifies an irreducible Markov chain on a countable state space $S$ (a quasi-birth-and-death process, and the restricted chain on its level $0$) as positive recurrent, null recurrent or transient. This file fixes those notions for a matrix $P = (P_{xy})_{x,y \in S}$ with $S$ an arbitrary countable type.
--
--   1. $P$ is **stochastic** if $P_{xy} \ge 0$ for all $x, y$ and every row sums to one, $\sum_{y} P_{xy} = 1$.
--   2. The $t$-step transition probabilities are $P_{xy}(0) = \delta_{xy}$ and $P_{xy}(t+1) = \sum_{z} P_{xz}(t) P_{zy}$; $P$ is **irreducible** if for all $x, y$ there is $t \ge 0$ with $P_{xy}(t) > 0$.
--   3. The weight of a finite trajectory $\omega_0, \dots, \omega_t$ is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$, and $\mathrm P_x[\tau^+_A > t]$ is the sum of the weights of the trajectories starting at $x$ that avoid the set $A$ at times $1, \dots, t$. With $A = \{x\}$ this is the tail of the first return time $\tau^+_x$ to $x$.
--   4. A state $x$ is **recurrent** if $\mathrm P_x[\tau^+_x > t] \to 0$ as $t \to \infty$ (the chain returns to $x$ with probability one), and **positive recurrent** if $\sum_{t \ge 0} \mathrm P_x[\tau^+_x > t] < \infty$ (the expected return time is finite).
--   5. A **stationary probability vector** is a row vector $\pi$ with $\pi \ge 0$, $\pi\mathbf 1 = 1$ and $\pi P = \pi$.
--   6. The chain is **recurrent**, **positive recurrent**, **null recurrent** (recurrent but not positive recurrent) or **transient** (not recurrent) when every state has that property.
--
--   For an irreducible chain each of the four chain-level properties holds for every state as soon as it holds for one, so item 6 is the usual meaning of "the QBD is positive recurrent" and so on.
--
--   **Formalization Note** The bodies of items 1–5 are those of the public platform definition `mm_countable` (namespace `MarkovMixing`), restated in the namespace `MatrixAnalytic.Stability` because that module is not importable in this environment. The sums are Lean's `tsum`/`HasSum`, over trajectory sums of nonnegative terms. When $P$ is substochastic (row sums at most one), the same formulas count the lost mass as a failure to return, which is the meaning used for the restricted chain $P^{\{0\}}$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 130 (setting) and pp. 147–149 (Chapter 7); bodies restated from the platform definition mm_countable (Levin–Peres–Wilmer, Markov Chains and Mixing Times, Ch. 21)

import Mathlib

namespace MatrixAnalytic.Stability

noncomputable section

/-!
Markov chains on a countable state space, the setting of Chapter 7 of Latouche & Ramaswami
(an irreducible QBD is a chain on the countable set of states `(n, i)`, `n ≥ 0`, with finitely or
infinitely many phases `i`; the restricted chain `P^{0}` lives on the phases of level `0`).
The bodies of `IsStochasticC` … `IsStationaryC` are those of the platform definition
`mm_countable` (namespace `MarkovMixing`), restated here because that module is not available as
an import. The four chain-level properties at the end say that *every* state is recurrent,
positive recurrent, null recurrent or transient; for an irreducible chain each of them is
equivalent to the same property of a single state.
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
two states", p. 130). -/
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

/-- A state is **recurrent** if `P_x[τ⁺_x < ∞] = 1`, i.e. the return-time tails tend to `0`. -/
def Recurrent (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)

/-- A state is **positive recurrent** if its expected first return time is finite, i.e. the
return-time tails are summable. -/
def PositiveRecurrent (P : V → V → ℝ) (x : V) : Prop :=
  Summable fun t => returnTailC P x t

/-- A stationary probability vector: `π ≥ 0`, `π1 = 1` and `πP = π`. -/
def IsStationaryC (P : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧
    ∀ y : V, HasSum (fun x => π x * P x y) (π y)

/-- The chain is **recurrent**: every state is recurrent. -/
def IsRecurrentChain (P : V → V → ℝ) : Prop :=
  ∀ x : V, Recurrent P x

/-- The chain is **positive recurrent**: every state is positive recurrent. -/
def IsPositiveRecurrentChain (P : V → V → ℝ) : Prop :=
  ∀ x : V, PositiveRecurrent P x

/-- The chain is **null recurrent**: every state is recurrent but not positive recurrent. -/
def IsNullRecurrentChain (P : V → V → ℝ) : Prop :=
  ∀ x : V, Recurrent P x ∧ ¬ PositiveRecurrent P x

/-- The chain is **transient**: no state is recurrent. -/
def IsTransientChain (P : V → V → ℝ) : Prop :=
  ∀ x : V, ¬ Recurrent P x

end

end MatrixAnalytic.Stability


