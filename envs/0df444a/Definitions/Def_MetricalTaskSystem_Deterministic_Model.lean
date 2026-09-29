-- Prove2me | Definitions.Def_MetricalTaskSystem_Deterministic_Model
-- name    : MetricalTaskSystem_Deterministic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:08:40.242985+00:00
-- url     : https://prove2.me/theorems/1429cf1d-d99d-4f55-bd81-d19287986892
-- title:
--   Task systems, schedules, on-line algorithms and the competitive ratio $w(S,d)$
-- statement:
--   This file sets up the model of Borodin, Linial and Saks.
--
--   A **task system** $(S,d)$ consists of a finite set $S$ of $n$ states and a transition-cost matrix $d : S\times S\to\mathbb R$ with $d(i,i)=0$, $d(i,j)>0$ for $i\neq j$, and the triangle inequality $d(i,j)+d(j,k)\ge d(i,k)$. It is **metrical** if moreover $d(i,j)=d(j,i)$.
--
--   A task is a vector $T=(T(s))_{s\in S}$ of nonnegative processing costs. For a task sequence $\mathbf T=T^1T^2\cdots T^m$ with initial state $s_0$, a **schedule** is a map $\sigma:\{0,\dots,m\}\to S$ with $\sigma(0)=s_0$, where $\sigma(i)$ is the state in which $T^i$ is processed. Its cost is
--   $$c(\mathbf T;\sigma)=\sum_{i=1}^m d(\sigma(i-1),\sigma(i))+\sum_{i=1}^m T^i(\sigma(i)),$$
--   and the off-line optimum $c_0(\mathbf T)$ is the minimum of $c(\mathbf T;\sigma)$ over all schedules.
--
--   An **on-line algorithm** $A$ chooses $\sigma(i)$ as a function of $s_0$ and the first $i$ tasks $T^1,\dots,T^i$ only; $c_A(\mathbf T)$ is the cost of the schedule it produces. For $w>0$, $A$ is **$w$-competitive** if there is a constant $K_w$ with
--   $$c_A(\mathbf T)\le w\,c_0(\mathbf T)+K_w$$
--   for every finite task sequence $\mathbf T$ (and every initial state). The **competitive ratio of the task system** is
--   $$w(S,d)=\inf_A \inf\{w : A \text{ is } w\text{-competitive}\},$$
--   the infimum over all on-line algorithms, with $\inf\emptyset=+\infty$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** States form a finite type `S`. Tasks are finite nonnegative reals (the paper also allows $+\infty$ entries; these are excluded). A task sequence of length $m$ is `T : Fin m → S → ℝ` with `T i` the paper's $T^{i+1}$; a schedule is `σ : Fin (m+1) → S`. An on-line algorithm is a map `S → List (S → ℝ) → S` sending $(s_0,[T^1,\dots,T^i])$ to $\sigma(i)$. The competitive ratio is the real infimum of the set of all $w$ for which some on-line algorithm is $w$-competitive; this has the same value as $\inf_A\inf W_A$ with the convention $\inf\emptyset=+\infty$ whenever some algorithm is competitive.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), pp. 746-747, Section 1

import Mathlib

namespace MetricalTaskSystem.Deterministic

/-- A **task system** `(S, d)` (Borodin–Linial–Saks 1992, p. 746): the transition-cost matrix
`d` has zero diagonal, positive off-diagonal entries and satisfies the triangle inequality
`d(i, j) + d(j, k) ≥ d(i, k)`. The state set `S` is a finite type (the paper's `{1, …, n}`). -/
structure IsTaskSystem {S : Type} (d : S → S → ℝ) : Prop where
  diag : ∀ i, d i i = 0
  pos : ∀ i j, i ≠ j → 0 < d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- A task system is **metrical** if, in addition, `d` is symmetric (p. 747). -/
def IsMetrical {S : Type} (d : S → S → ℝ) : Prop :=
  IsTaskSystem d ∧ ∀ i j, d i j = d j i

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

/-- An **on-line (deterministic, discrete-time) scheduling algorithm** (p. 747): the state
`σ(i)` is a function of the initial state `s₀` and of the first `i` tasks `T¹ ⋯ Tⁱ` only.
It is encoded as the map `(s₀, [T¹, …, Tⁱ]) ↦ σ(i)`; its value on the empty list is never
used, since `σ(0) = s₀`. -/
abbrev OnlineAlgorithm (S : Type) : Type := S → List (S → ℝ) → S

/-- The schedule `σ = A(T)` that the on-line algorithm `A` produces on `T¹ ⋯ Tᵐ` from `s₀`:
`σ(0) = s₀` and `σ(i) = A(s₀, [T¹, …, Tⁱ])` for `1 ≤ i ≤ m`. -/
def onlineSchedule {S : Type} (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) :
    Fin (m + 1) → S :=
  fun i => if (i : ℕ) = 0 then s₀ else A s₀ ((List.ofFn T).take i)

/-- The cost `c_A(T) = c(T; A(T))` of an on-line algorithm (p. 747). -/
def onlineCost {S : Type} (d : S → S → ℝ) (A : OnlineAlgorithm S) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) : ℝ :=
  schedCost d T (onlineSchedule A s₀ T)

/-- `A` is **`w`-competitive** (p. 747): `w > 0` and there is a constant `K` such that
`c_A(T) − w·c₀(T) ≤ K` for every finite task sequence `T` (with any initial state `s₀`).
Tasks are finite and nonnegative. The inequality is written additively. -/
def IsCompetitive {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ)
    (A : OnlineAlgorithm S) (w : ℝ) : Prop :=
  0 < w ∧ ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
    onlineCost d A s₀ T ≤ w * offlineOpt d s₀ T + K

/-- The **competitive ratio of the task system** `w(S, d)` (p. 747): the infimum over on-line
algorithms `A` of `w(A) = inf W_A`, where `W_A = {w : A is w-competitive}`. It is written as
the infimum of the union `⋃_A W_A`, which has the same value as `inf_A inf W_A` when
`inf ∅ = +∞`. (If no algorithm were competitive, the real `sInf ∅` would be `0`.) -/
noncomputable def competitiveRatio {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) : ℝ :=
  sInf {w : ℝ | ∃ A : OnlineAlgorithm S, IsCompetitive d A w}

end MetricalTaskSystem.Deterministic


