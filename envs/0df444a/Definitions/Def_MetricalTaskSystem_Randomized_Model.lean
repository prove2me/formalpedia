-- Prove2me | Definitions.Def_MetricalTaskSystem_Randomized_Model
-- name    : MetricalTaskSystem_Randomized_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:16:30.154216+00:00
-- url     : https://prove2.me/theorems/338c0a92-5251-4149-819d-b6d8bf59f428
-- title:
--   Task systems, schedules, off-line optimum, deterministic on-line algorithms and the uniform task system
-- statement:
--   This file sets up the deterministic model of Borodin, Linial and Saks, on which the randomized model of the mission is built.
--
--   A **task system** $(S,d)$ consists of a finite set $S$ of $n$ states and a transition-cost matrix $d : S\times S\to\mathbb R$ with $d(i,i)=0$, $d(i,j)>0$ for $i\neq j$, and the triangle inequality $d(i,j)+d(j,k)\ge d(i,k)$. The **uniform task system** is the one in which every state transition has unit cost:
--   $$d(i,j)=\begin{cases}0,& i=j,\\ 1,& i\neq j.\end{cases}$$
--
--   A task is a vector $T=(T(s))_{s\in S}$ of nonnegative processing costs. For a task sequence $\mathbf T=T^1T^2\cdots T^m$ and an initial state $s_0$, a **schedule** is a map $\sigma:\{0,\dots,m\}\to S$ with $\sigma(0)=s_0$; $\sigma(i)$ is the state in which $T^i$ is processed. Its cost is
--   $$c(\mathbf T;\sigma)=\sum_{i=1}^m d(\sigma(i-1),\sigma(i))+\sum_{i=1}^m T^i(\sigma(i)),$$
--   and the off-line optimum $c_0(\mathbf T)$ is the minimum of $c(\mathbf T;\sigma)$ over all schedules starting at $s_0$.
--
--   A **deterministic on-line algorithm** $A$ chooses $\sigma(i)$ as a function of $s_0$ and of the first $i$ tasks $T^1,\dots,T^i$ only (task $T^i$ is seen before $\sigma(i)$ is chosen); $c_A(\mathbf T)$ is the cost of the schedule it produces.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** States form a finite type `S`. Tasks are finite nonnegative reals (the paper also allows $+\infty$ entries; these are excluded). A task sequence of length $m$ is `T : Fin m → S → ℝ` with `T i` the paper's $T^{i+1}$; a schedule is `σ : Fin (m+1) → S`. The off-line optimum is a `Finset.inf'` over the nonempty finite set of schedules with `σ 0 = s₀`. A deterministic on-line algorithm is a map `S → List (S → ℝ) → S` sending $(s_0,[T^1,\dots,T^i])$ to $\sigma(i)$. The uniform task system is stated with unit transition cost, as in the paper.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), pp. 746-747, Section 1; p. 758, Section 7 (uniform task system)

import Mathlib

namespace MetricalTaskSystem.Randomized

/-- A **task system** `(S, d)` (Borodin–Linial–Saks 1992, p. 746): the transition-cost matrix
`d` has zero diagonal, positive off-diagonal entries ("for any two states `i ≠ j`, there is a
positive transition cost `d(i, j)`") and satisfies the triangle inequality
`d(i, j) + d(j, k) ≥ d(i, k)`. The state set `S` is a finite type (the paper's `{1, …, n}`). -/
structure IsTaskSystem {S : Type} (d : S → S → ℝ) : Prop where
  diag : ∀ i, d i i = 0
  pos : ∀ i j, i ≠ j → 0 < d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- The **uniform task system** (p. 758): every state transition has the same unit cost,
`d(i, j) = 1` for `i ≠ j` and `d(i, i) = 0`. -/
def uniformD {S : Type} [DecidableEq S] : S → S → ℝ :=
  fun i j => if i = j then 0 else 1

/-- The cost `c(T; σ)` of a schedule (p. 747) for a task sequence of length `m`.
Task `T i` (for `i : Fin m`) is the paper's `T^{i+1}`; a schedule is `σ : Fin (m+1) → S`,
where `σ 0` is the initial state and `σ (i+1)` is the state in which `T^{i+1}` is processed:
`c(T; σ) = Σ_{i=1}^m d(σ(i−1), σ(i)) + Σ_{i=1}^m T^i(σ(i))`. -/
def schedCost {S : Type} (d : S → S → ℝ) {m : ℕ} (T : Fin m → S → ℝ)
    (σ : Fin (m + 1) → S) : ℝ :=
  ∑ i : Fin m, (d (σ i.castSucc) (σ i.succ) + T i (σ i.succ))

/-- The optimal off-line cost `c₀(T)` (p. 747): the minimum of `c(T; σ)` over the finitely many
schedules `σ` with `σ 0 = s₀`. -/
noncomputable def offlineOpt {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ) (s₀ : S)
    {m : ℕ} (T : Fin m → S → ℝ) : ℝ :=
  (Finset.univ.filter (fun σ : Fin (m + 1) → S => σ 0 = s₀)).inf'
    ⟨fun _ => s₀, by simp⟩ (fun σ => schedCost d T σ)

/-- A **deterministic on-line scheduling algorithm** (p. 747): the state `σ(i)` is a function of
the initial state `s₀` and of the first `i` tasks `T¹ ⋯ Tⁱ` only. It is encoded as the map
`(s₀, [T¹, …, Tⁱ]) ↦ σ(i)`; its value on the empty list is never used, since `σ(0) = s₀`. -/
abbrev OnlineAlgorithm (S : Type) : Type := S → List (S → ℝ) → S

/-- The schedule `σ = A(T)` that the on-line algorithm `A` produces on `T¹ ⋯ Tᵐ` from `s₀`:
`σ(0) = s₀` and `σ(i) = A(s₀, [T¹, …, Tⁱ])` for `1 ≤ i ≤ m`. -/
def onlineSchedule {S : Type} (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) :
    Fin (m + 1) → S :=
  fun i => if (i : ℕ) = 0 then s₀ else A s₀ ((List.ofFn T).take i)

/-- The cost `c_A(T) = c(T; A(T))` of a deterministic on-line algorithm (p. 747). -/
def onlineCost {S : Type} (d : S → S → ℝ) (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) : ℝ :=
  schedCost d T (onlineSchedule A s₀ T)

end MetricalTaskSystem.Randomized


