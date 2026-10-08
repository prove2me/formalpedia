-- Prove2me | Definitions.Def_LogicBenders_Generic_Setting
-- name    : LogicBenders_Generic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:35.331465+00:00
-- url     : https://prove2.me/theorems/f3b8fe17-9911-4a7c-b4e2-1817723d2f48
-- title:
--   §3, §5 and Fig. 1, pp. 5–9 — inference dual, problem (6), subproblem (7) and its dual (8), master problem (9), (B1), and a run of the generic Benders algorithm
-- statement:
--   This file sets up the objects of §3 and §5 of Hooker and Ottosson's *Logic-based Benders decomposition*: the inference dual of an optimization problem, the decomposed problem (6), its subproblem (7) and the subproblem's inference dual (8), the master problem (9), the validity condition (B1) on a Benders cut, and a run of the generic Benders algorithm of Figure 1.
--
--   **Optimal values.** All optimal values are extended reals in $[-\infty, +\infty]$, following the convention of §3: a minimization problem has optimal value $+\infty$ when it is infeasible and $-\infty$ when it is unbounded, and vice versa for a maximization problem.
--
--   **Problem (1) and its inference dual (2).** Let $D$ be a domain, $S \subseteq D$ a feasible set and $f : D \to \mathbb R$ an objective. For propositions $P, Q$ depending on $x$, $P$ *implies $Q$ with respect to $D$*, written $P \xrightarrow{D} Q$, if $Q(x)$ holds for every $x \in D$ at which $P(x)$ holds. The optimal value of problem (1) is
--   $$\operatorname{val}(1) = \inf_{x \in S} f(x) \in [-\infty, +\infty],$$
--   and the optimal value of its inference dual (2), $\max \beta$ subject to $x \in S \xrightarrow{D} f(x) \ge \beta$, is the supremum of all extended reals $\beta$ such that $f(x) \ge \beta$ for every $x \in S$.
--
--   **Problem (6), subproblem (7), dual (8).** Let $D_x, D_y$ be domains, $S \subseteq D_x \times D_y$ and $f : D_x \times D_y \to \mathbb R$. Problem (6) is $\min f(x,y)$ over $(x,y) \in S$, with optimal value $\inf_{(x,y) \in S} f(x,y)$; it is *unbounded* if for every real $M$ some $(x,y) \in S$ has $f(x,y) < M$. For a trial value $\bar y \in D_y$, the subproblem (7) is $\min f(x,\bar y)$ over $\{x : (x,\bar y) \in S\}$, with optimal value $\inf_{(x,\bar y) \in S} f(x,\bar y)$. An extended real $\beta$ is *feasible* in the subproblem dual (8) if $(x,\bar y) \in S \xrightarrow{D_x} f(x,\bar y) \ge \beta$, and *optimal* if it is feasible and at least every feasible value; the optimal value $\beta^*$ of (8) is the supremum of its feasible values. Note that $\beta = -\infty$ is always feasible, and $\beta = +\infty$ is feasible exactly when the subproblem is infeasible.
--
--   **Benders cuts and (B1).** A bounding function is a map $\beta_{\bar y} : D_y \to [-\infty, +\infty]$; the Benders cut it defines is $z \ge \beta_{\bar y}(y)$. Condition **(B1)** says the cut is *valid*: every feasible $(x,y)$ of (6) satisfies $f(x,y) \ge \beta_{\bar y}(y)$.
--
--   **Master problem (9).** With bounding functions $\beta^{(0)}, \dots, \beta^{(k)}$ already generated, the master problem is $\min z$ subject to $z \ge \beta^{(j)}(y)$ for $j = 0, \dots, k$, $y \in D_y$. Write $L_k(y) = \max_{0 \le j \le k} \beta^{(j)}(y)$. The master is *infeasible* if $L_k(y) = +\infty$ for every $y$. A pair $(z, \bar y)$ is an *optimal solution with optimal value $z$* if $z = L_k(\bar y) < +\infty$ and $z \le L_k(y)$ for every $y$; $z = -\infty$ is the value of an unbounded master.
--
--   **A run of Figure 1.** Iterations are numbered $k = 0, 1, 2, \dots$. A run consists of trial values $\bar y_k$, bounds $\bar z_k$, dual values $\beta_k$ and bounding functions $\beta^{(k)}$. Iteration $k$ *continues* if $\beta_k$ is feasible in (8) at $\bar y_k$, $\beta_k > \bar z_k$, and $\beta^{(k)}(\bar y_k) = \beta_k$ (the While test of Figure 1 and "Formulate a lower bound function $\beta_{\bar y}(y)$ with $\beta_{\bar y}(\bar y) = \beta$"). The data form a run through $N$ iterations if $\bar z_0 = -\infty$ and, for each $k < N$, iteration $k$ continues and $(\bar z_{k+1}, \bar y_{k+1})$ is an optimal solution of the master with the cuts $0, \dots, k$. The run *stops at the While test* at iteration $N$ if, in addition, no $\beta$ feasible in (8) at $\bar y_N$ satisfies $\beta > \bar z_N$; it *stops with an infeasible master* at iteration $N$ if iteration $N$ continues and the master with the cuts $0, \dots, N$ is infeasible.
--
--   These objects are the vocabulary of Theorems 1 and 2 of the paper, the correctness and finite-termination results for the generic logic-based Benders algorithm.
--
--   **Formalization Note.** Domains are Lean types (`X` for $D_x$, `Y` for $D_y$, `D` for $D$), so a feasible set is a set of elements of the domain. Optimal values are `EReal` infima and suprema. Iterations are 0-based: the paper's $k$-th cut $\beta_{y^k}$ is `cut (k-1)`, generated at `ybar (k-1)`.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), pp. 5–9, §3 displays (1)–(2) and the optimal-value convention (p. 6), §5 displays (6)–(9), condition (B1) (p. 9), Figure 1 (p. 9)

import Mathlib

namespace LogicBenders.Generic

/-! ### §3: problem (1) and its inference dual (2)

Optimal values live in `EReal`: by the convention of §3 (p. 6) a minimization problem has value
`⊤` (= +∞) when infeasible and `⊥` (= −∞) when unbounded, and vice versa for a maximization. -/

/-- Semantic implication with respect to the domain `D` (§3, p. 6): `P →_D Q` holds when `Q x`
is true for every `x : D` at which `P x` is true. -/
def ImpliesWrt {D : Type*} (P Q : D → Prop) : Prop :=
  ∀ x : D, P x → Q x

/-- The optimal value of problem (1), `min f(x)` s.t. `x ∈ S`, `x ∈ D`, in `EReal`:
`⊤` if `S` is empty, `⊥` if `f` is unbounded below on `S`. -/
noncomputable def optVal1 {D : Type*} (S : Set D) (f : D → ℝ) : EReal :=
  ⨅ x ∈ S, (f x : EReal)

/-- The optimal value of the inference dual (2), `max β` s.t. `x ∈ S →_D f(x) ≥ β`:
the supremum, in `EReal`, of every `β` for which `f(x) ≥ β` is implied by `x ∈ S`. -/
noncomputable def infDualVal1 {D : Type*} (S : Set D) (f : D → ℝ) : EReal :=
  sSup {β : EReal | ImpliesWrt (fun x => x ∈ S) (fun x => β ≤ (f x : EReal))}

/-! ### §5: problem (6), the subproblem (7) and its inference dual (8) -/

/-- The optimal value of problem (6), `min f(x, y)` s.t. `(x, y) ∈ S`, `x ∈ D_x`, `y ∈ D_y`. -/
noncomputable def optVal {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) : EReal :=
  ⨅ p ∈ S, (f p.1 p.2 : EReal)

/-- The optimal value of the subproblem (7) at the trial value `yb` (the paper's `ȳ`):
`min f(x, ȳ)` s.t. `(x, ȳ) ∈ S`, `x ∈ D_x`. -/
noncomputable def subVal {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) : EReal :=
  ⨅ x ∈ {x : X | (x, yb) ∈ S}, (f x yb : EReal)

/-- `β` is a feasible solution of the subproblem dual (8) at `yb`:
`(x, ȳ) ∈ S →_{D_x} f(x, ȳ) ≥ β`. -/
def IsDualFeasible {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) (β : EReal) : Prop :=
  ImpliesWrt (fun x : X => (x, yb) ∈ S) (fun x => β ≤ (f x yb : EReal))

/-- `β` is an optimal solution of the subproblem dual (8) at `yb`. -/
def IsDualOptimal {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) (β : EReal) : Prop :=
  IsDualFeasible S f yb β ∧ ∀ β' : EReal, IsDualFeasible S f yb β' → β' ≤ β

/-- The optimal value `β*` of the subproblem dual (8) at `yb`. -/
noncomputable def subDualVal {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y) : EReal :=
  sSup {β : EReal | IsDualFeasible S f yb β}

/-- Condition (B1) for one bounding function `g = β_ȳ`: the Benders cut `z ≥ g(y)` is valid,
i.e. every feasible `(x, y)` of (6) satisfies `f(x, y) ≥ g(y)`. -/
def ValidCut {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (g : Y → EReal) : Prop :=
  ∀ (x : X) (y : Y), (x, y) ∈ S → g y ≤ (f x y : EReal)

/-- Problem (6) is unbounded: its objective takes arbitrarily negative values on `S`. -/
def IsUnbounded {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) : Prop :=
  ∀ M : ℝ, ∃ (x : X) (y : Y), (x, y) ∈ S ∧ f x y < M

/-! ### The master problem (9) -/

/-- The largest right-hand side of the master constraints `z ≥ β_{y^j}(y)` after the cuts of
iterations `0, …, k` (0-based): a real `z` is feasible with `y` iff `masterLHS cut k y ≤ z`. -/
noncomputable def masterLHS {Y : Type*} (cut : ℕ → Y → EReal) (k : ℕ) (y : Y) : EReal :=
  ⨆ j ∈ Finset.range (k + 1), cut j y

/-- The master problem (9) with the cuts `0, …, k` is infeasible: no `y` admits a real `z`. -/
def MasterInfeasible {Y : Type*} (cut : ℕ → Y → EReal) (k : ℕ) : Prop :=
  ∀ y : Y, masterLHS cut k y = ⊤

/-- `(z, y)` is an optimal solution of the master problem (9) with the cuts `0, …, k`, with
optimal value `z`. The value `z = ⊥` is the `−∞` of an unbounded master (§3 convention). -/
def IsMasterOptimal {Y : Type*} (cut : ℕ → Y → EReal) (k : ℕ) (z : EReal) (y : Y) : Prop :=
  z = masterLHS cut k y ∧ z < ⊤ ∧ ∀ y' : Y, z ≤ masterLHS cut k y'

/-! ### A run of the generic Benders algorithm (Figure 1, p. 9)

Iterations are indexed `k = 0, 1, …`. Iteration `k` works at the trial value `ybar k` with the
incumbent bound `zbar k`; if it continues, it finds a dual-feasible `beta k > zbar k` and adds the
cut `cut k` (the paper's `β_{y^{k+1}}`, with `y^{k+1} = ybar k`). -/

/-- The data of a run of the generic Benders algorithm. -/
structure Run (Y : Type*) where
  /-- The trial value `ȳ` at iteration `k`; `ybar 0` is the initial choice. -/
  ybar : ℕ → Y
  /-- The bound `z̄` at iteration `k`. -/
  zbar : ℕ → EReal
  /-- The dual-feasible value `β` found at iteration `k`. -/
  beta : ℕ → EReal
  /-- The bounding function `β_ȳ` formulated at iteration `k`. -/
  cut : ℕ → Y → EReal

/-- Iteration `k` passes the While test of Figure 1 and formulates its cut: `beta k` is feasible
in (8) at `ybar k`, `beta k > zbar k`, and `cut k (ybar k) = beta k`. -/
def ContinuesAt {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (k : ℕ) : Prop :=
  IsDualFeasible S f (r.ybar k) (r.beta k) ∧ r.zbar k < r.beta k ∧ r.cut k (r.ybar k) = r.beta k

/-- `r` is a run of Figure 1 through `N` completed iterations: `z̄ = −∞` at the start, and each
iteration `k < N` passes the While test, adds its cut, finds the master (9) with the cuts
`0, …, k` feasible, and takes `(zbar (k+1), ybar (k+1))` as an optimal solution of it. -/
def IsRun {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (N : ℕ) : Prop :=
  r.zbar 0 = ⊥ ∧
    ∀ k < N, ContinuesAt S f r k ∧ IsMasterOptimal r.cut k (r.zbar (k + 1)) (r.ybar (k + 1))

/-- The run stops at iteration `N` because the While test fails: the subproblem dual (8) at
`ybar N` has no feasible solution `β > zbar N`. -/
def StopsAtWhile {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (N : ℕ) : Prop :=
  IsRun S f r N ∧ ¬ ∃ β : EReal, IsDualFeasible S f (r.ybar N) β ∧ r.zbar N < β

/-- The run stops at iteration `N` with an infeasible master: iteration `N` passes the While
test and adds its cut, and the master (9) with the cuts `0, …, N` is infeasible. -/
def StopsAtMaster {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (r : Run Y) (N : ℕ) : Prop :=
  IsRun S f r N ∧ ContinuesAt S f r N ∧ MasterInfeasible r.cut N

end LogicBenders.Generic


