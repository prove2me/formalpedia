-- Prove2me | Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting
-- name    : HeldWolfeCrowder_CoreProblem_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:48:20.467857+00:00
-- url     : https://prove2.me/theorems/fee88cfb-487d-42e0-882b-ab73dd822c0c
-- title:
--   The function w of Eq. (2.2), the subgradient run (2.5)–(2.7), the dual LP (6.1) and the core problem P(J, J*)
-- statement:
--   This file fixes the objects of Held, Wolfe & Crowder's analysis of the subgradient method for maximizing a piecewise-linear concave function, and of the linear programs of their Section 6.
--
--   Let $E^n=\mathbb R^n$ with the Euclidean inner product $\pi\cdot v$. The data are finitely many scalars $c_k\in\mathbb R$ and vectors $v_k\in E^n$, $k=1,\dots,K$, with $K\ge 1$.
--
--   1. **The function (2.2).** For $\pi\in E^n$,
--   $$w(\pi)=\min\{c_k+\pi\cdot v_k : k=1,\dots,K\}.$$
--   2. **Minimizing indices (2.3).** The index $k$ *attains the minimum at $\pi$* if $c_k+\pi\cdot v_k=w(\pi)$, i.e. $v_k\in V(\pi)$.
--   3. **The subgradient algorithm (2.5)–(2.6).** A run consists of step sizes $t_j$, iterates $\pi^j$ ($j=0,1,\dots$) and indices $k(j)$ such that $t_j>0$, the index $k(j)$ attains the minimum at $\pi^j$, and
--   $$\pi^{j+1}=\pi^j+t_j\,v_{k(j)}\qquad (j=0,1,\dots).$$
--   The starting point $\pi^0$ is arbitrary, and no rule for choosing $k(j)$ among the minimizing indices is imposed. One writes $v^j=v_{k(j)}$ and $c^j=c_{k(j)}$.
--   4. **Step-size conditions (2.7).** $t_j\to 0$ and $\sum_{j=0}^\infty t_j=\infty$.
--   5. **The dual linear program (6.1).**
--   $$\min\Big\{\sum_k c_k y_k : y_k\ge 0,\ \sum_k y_k=1,\ \sum_k y_k v_k=0\Big\},$$
--   the linear-programming dual of $\max\{z : z-\pi\cdot v_k\le c_k \text{ for all } k\}$, i.e. of $\max_\pi w(\pi)$. A *solution* of (6.1) is a feasible $y$ whose objective is no larger than that of any feasible point.
--   6. **The core problem $P(J,J^*)$.** For integers $J<J^*$, the linear program in the variables $y_j$, $J\le j\le J^*$, indexed by iterations,
--   $$\min\Big\{\sum_{j=J}^{J^*} c^j y_j : y_j\ge 0,\ \sum_{j=J}^{J^*} y_j=1,\ \sum_{j=J}^{J^*} y_j v^j=0\Big\}.$$
--   An iteration whose index was already chosen earlier contributes a further, identical column.
--   7. **Aggregation.** A point $y$ of $P(J,J^*)$ is sent to the point of (6.1) with coordinates $\bar y_k=\sum\{y_j : J\le j\le J^*,\ k(j)=k\}$. This map preserves feasibility and the objective value; it is how "a solution of $P(J,J^*)$ solves (6.1)" is read.
--
--   These definitions are shared by every statement of the mission: the convergence of the method, the duality between $\max w$ and (6.1), and the optimality certificate given by the core problem.
--
--   **Formalization Note** $E^n$ is `EuclideanSpace ℝ (Fin n)` and the index set $\{1,\dots,K\}$ is a finite nonempty type `ι`; $w$ is the finite minimum `Finset.univ.inf'`. The equality constraints of (6.1) and $P(J,J^*)$, printed as $\sum -v_k y_k=0$, are written $\sum y_k v_k=0$. $\sum t_j=\infty$ is stated as divergence of the partial sums to $+\infty$ (equivalent to non-summability for positive $t_j$). The variables of $P(J,J^*)$ are a function on $\mathbb N$ of which only the values at $J\le j\le J^*$ enter; the definition itself does not require $J<J^*$, which every statement using it imposes.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 64, Eqs. (2.2), (2.3); p. 66, Eqs. (2.5), (2.6); p. 67, Eq. (2.7); p. 81, Eq. (6.1) and the definition of P(J, J*)

import Mathlib

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Eq. (2.2), p. 64.** The piecewise-linear concave function
`w(π) = min { c_k + π·v_k : k = 1, …, K }` on `Eⁿ = EuclideanSpace ℝ (Fin n)`, for data
`c : ι → ℝ`, `v : ι → Eⁿ` indexed by a finite nonempty type `ι` (the paper's `{1, …, K}`). -/
noncomputable def w {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (π : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => c k + ⟪π, v k⟫_ℝ)

/-- **Eq. (2.3), p. 64.** The index `k` attains the minimum in (2.2) at `π`, i.e.
`c_k + π·v_k = w(π)`, i.e. `v_k ∈ V(π)`. -/
def IsMinIndex {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (π : EuclideanSpace ℝ (Fin n)) (k : ι) :
    Prop :=
  c k + ⟪π, v k⟫_ℝ = w c v π

/-- **The subgradient algorithm (2.5)–(2.6), p. 66.** A run of the method: positive step sizes
`t_j`, an index `k(j)` chosen at step `j` that attains the minimum (2.2) at `π^j`
(so `v(π^j) = v_{k(j)} ∈ V(π^j)`, (2.5)), and the update `π^{j+1} = π^j + t_j v(π^j)`
for `j = 0, 1, …` (2.6). The starting point `π^0 = π 0` is arbitrary. -/
structure IsSubgradientRun {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) : Prop where
  /-- The step sizes are positive scalars. -/
  step_pos : ∀ j, 0 < t j
  /-- `k(j)` attains the minimum in (2.2) at `π^j`. -/
  index_min : ∀ j, IsMinIndex c v (π j) (k j)
  /-- The update (2.6). -/
  step : ∀ j, π (j + 1) = π j + t j • v (k j)

/-- **Step-size conditions (2.7), p. 67.** `t_j → 0` and `Σ_{j=0}^∞ t_j = ∞`, the latter stated
as: the partial sums `Σ_{j<N} t_j` tend to `+∞`. -/
def StepSizeCond (t : ℕ → ℝ) : Prop :=
  Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ j ∈ Finset.range N, t j) atTop atTop

/-- **The dual linear program (6.1), p. 81: feasibility.** `y_k ≥ 0` for all `k`,
`Σ_k y_k = 1` and `Σ_k −v_k y_k = 0` (written here as `Σ_k y_k v_k = 0`). -/
def DualFeasible {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) : Prop :=
  (∀ k, 0 ≤ y k) ∧ ∑ k, y k = 1 ∧ ∑ k, y k • v k = 0

/-- **(6.1): objective** `Σ_k c_k y_k`. -/
def dualObj {ι : Type*} [Fintype ι] (c : ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ k, c k * y k

/-- **(6.1): optimality.** `y` is feasible for (6.1) and minimizes `Σ_k c_k y_k` over all
feasible points, i.e. `y` solves (6.1). -/
def IsDualOptimal {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) : Prop :=
  DualFeasible v y ∧ ∀ y' : ι → ℝ, DualFeasible v y' → dualObj c y ≤ dualObj c y'

/-- **The core problem `P(J, J*)`, p. 81: feasibility.** The variables `y_j` are indexed by the
iterations `j ∈ [J, J*]` (values of `y` outside `[J, J*]` play no role); with
`v^j = v_{k(j)}`, the constraints are `y_j ≥ 0` for `J ≤ j ≤ J*`, `Σ_{j=J}^{J*} y_j = 1` and
`Σ_{j=J}^{J*} −v^j y_j = 0` (written here as `Σ_{j=J}^{J*} y_j v^j = 0`). Repeated indices
`k(j)` give repeated columns; nothing is deduplicated. -/
def CoreFeasible {n : ℕ} {ι : Type*}
    (v : ι → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ j ∈ Finset.Icc J Jstar, 0 ≤ y j) ∧
    ∑ j ∈ Finset.Icc J Jstar, y j = 1 ∧
    ∑ j ∈ Finset.Icc J Jstar, y j • v (k j) = 0

/-- **`P(J, J*)`: objective** `Σ_{j=J}^{J*} c^j y_j` with `c^j = c_{k(j)}`. -/
def coreObj {ι : Type*} (c : ι → ℝ) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc J Jstar, c (k j) * y j

/-- **`P(J, J*)`: optimality.** `y` is feasible for `P(J, J*)` and minimizes its objective over
all feasible points, i.e. `y` is a solution of `P(J, J*)`. -/
def IsCoreOptimal {n : ℕ} {ι : Type*}
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) :
    Prop :=
  CoreFeasible v k J Jstar y ∧
    ∀ y' : ℕ → ℝ, CoreFeasible v k J Jstar y' → coreObj c k J Jstar y ≤ coreObj c k J Jstar y'

open Classical in
/-- **Aggregation of a point of `P(J, J*)` to a point of (6.1).** The weight of index `i` is the
total weight of the iterations `j ∈ [J, J*]` at which `i` was chosen:
`y_i = Σ { y_j : J ≤ j ≤ J*, k(j) = i }`. This map carries feasible points of `P(J, J*)` to
feasible points of (6.1) with the same objective value; it is how "a solution of `P(J, J*)`
solves (6.1)" is read. -/
noncomputable def aggregate {ι : Type*} (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : ι → ℝ :=
  fun i => ∑ j ∈ (Finset.Icc J Jstar).filter (fun j => k j = i), y j

end HeldWolfeCrowder.CoreProblem


