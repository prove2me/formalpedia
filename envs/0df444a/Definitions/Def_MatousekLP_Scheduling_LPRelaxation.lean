-- Prove2me | Definitions.Def_MatousekLP_Scheduling_LPRelaxation
-- name    : MatousekLP_Scheduling_LPRelaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T12:27:51.267993+00:00
-- url     : https://prove2.me/theorems/81b9777e-05d1-4632-a511-90ff3ca42497
-- title:
--   The LP relaxation LPR(T), Assumption 8.3.1 and the support graph
-- statement:
--   Fix running times $d_{ij}$ ($i \in M$ machines, $j \in J$ jobs) and a threshold $T \in \mathbb{R}$. The linear program $\mathrm{LPR}(T)$ in the variables $t$ and $x_{ij}$ is
--   $$
--   \begin{aligned}
--   \text{minimize } \ & t \\
--   \text{subject to } \ & \textstyle\sum_{i \in M} x_{ij} = 1 && \text{for all } j \in J,\\
--   & \textstyle\sum_{j \in J} d_{ij} x_{ij} \le t && \text{for all } i \in M,\\
--   & x_{ij} \ge 0 && \text{for all } i \in M,\ j \in J,\\
--   & x_{ij} = 0 && \text{for all } i \in M,\ j \in J \text{ with } d_{ij} > T.
--   \end{aligned}
--   $$
--   A pair $(t, x)$ satisfying the constraints is **feasible**; it is **optimal** if moreover $t \le t'$ for every feasible $(t', x')$.
--
--   The **constraint matrix** $A$ of $\mathrm{LPR}(T)$, restricted to the columns of the variables $x_{ij}$, has one row for each machine, one for each job, and one for each pair $(i, j)$ with $d_{ij} > T$; the nonnegativity constraints are not rows. The column of $x_{ij}$ has entry $d_{ij}$ in the row of machine $i$, entry $1$ in the row of job $j$, entry $1$ in the row of the constraint $x_{ij} = 0$ (when $d_{ij} > T$), and $0$ elsewhere.
--
--   **Assumption 8.3.1** for a solution $x$: the columns of $A$ corresponding to the nonzero variables $x_{ij}$ are linearly independent. It holds for basic feasible solutions.
--
--   The **support graph** of $x$ is the bipartite graph $G = (M \cup J, E)$ with $E = \{\{i, j\} : x_{ij} > 0\}$.
--
--   **Formalization Note** Machines are `Fin m`, jobs `Fin n`; the edge $\{i,j\}$ is the pair `(i, j) : Fin m × Fin n`. The rows of $A$ are indexed by `Fin m ⊕ Fin n ⊕ {(i, j) // T < d i j}`; the column of the variable $t$ is not part of $A$ here, as it is not among the columns of Assumption 8.3.1. The optimal value $t^*(T)$ is never written as an infimum: statements quantify over optimal solutions of $\mathrm{LPR}(T)$, and $\mathrm{LPR}(T)$ having no optimal solution plays the role of the book's convention $t^*(T) = \infty$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 151 (LPR(T) and Assumption 8.3.1), pp. 151–152 (graph G), p. 152 (constraint matrix A, proof of Lemma 8.3.2)

import Mathlib

namespace MatousekLP.Scheduling

/-- Feasibility for the linear program `LPR(T)` of Matoušek–Gärtner §8.3 (p. 151), in the
variables `t` and `x i j` (machine `i : Fin m`, job `j : Fin n`):
`∑_i x_ij = 1` for every job `j`, `∑_j d_ij x_ij ≤ t` for every machine `i`,
`x_ij ≥ 0`, and `x_ij = 0` whenever `d_ij > T`. -/
def LPRFeasible {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (T t : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ j : Fin n, ∑ i : Fin m, x i j = 1) ∧
  (∀ i : Fin m, ∑ j : Fin n, d i j * x i j ≤ t) ∧
  (∀ i j, 0 ≤ x i j) ∧
  (∀ i j, T < d i j → x i j = 0)

/-- `(t, x)` is an optimal solution of `LPR(T)` ("Minimize t"): it is feasible and its value
`t` is at most the value `t'` of every feasible solution `(t', x')`. -/
def LPROptimal {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (T t : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  LPRFeasible d T t x ∧
    ∀ (t' : ℝ) (x' : Matrix (Fin m) (Fin n) ℝ), LPRFeasible d T t' x' → t ≤ t'

/-- The constraint matrix `A` of `LPR(T)` restricted to the columns of the variables `x_ij`
(proof of Lemma 8.3.2, p. 152). It has one row for each machine (`Sum.inl i`), one for each
job (`Sum.inr (Sum.inl j)`), and one for each pair `(i, j)` with `d_ij > T`
(`Sum.inr (Sum.inr p)`); the nonnegativity constraints are not rows. The entry in the
column of `x_ij` is `d_ij` in the row of machine `i`, `1` in the row of job `j`, `1` in the
row of the constraint `x_ij = 0` (if present), and `0` elsewhere. -/
def constraintMatrix {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (T : ℝ) :
    Matrix (Fin m ⊕ Fin n ⊕ {p : Fin m × Fin n // T < d p.1 p.2}) (Fin m × Fin n) ℝ :=
  Matrix.of fun r c =>
    match r with
    | Sum.inl i => if c.1 = i then d c.1 c.2 else 0
    | Sum.inr (Sum.inl j) => if c.2 = j then 1 else 0
    | Sum.inr (Sum.inr p) => if c = p.1 then 1 else 0

/-- Assumption 8.3.1 (p. 151): the columns of the constraint matrix `A` of `LPR(T)`
corresponding to the nonzero variables `x_ij` of the solution `x` are linearly independent.
(The column of the variable `t` is not among them.) -/
def Assumption831 {m n : ℕ} (d : Matrix (Fin m) (Fin n) ℝ) (T : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  LinearIndependent ℝ
    (fun c : {c : Fin m × Fin n // x c.1 c.2 ≠ 0} => fun r => constraintMatrix d T r c.1)

/-- The edge set `E = {{i, j} : x_ij > 0}` of the bipartite support graph `G = (M ∪ J, E)`
of a solution `x` (pp. 151–152), with the edge `{i, j}` written as the pair `(i, j)`. -/
noncomputable def supportEdges {m n : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun c => 0 < x c.1 c.2)

end MatousekLP.Scheduling


