-- Prove2me | Definitions.Def_HetImpatient_FluidSplit_Model
-- name    : HetImpatient_FluidSplit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:17.054538+00:00
-- url     : https://prove2.me/theorems/d606edf0-3a34-4a57-b595-68f03ae1aeb3
-- title:
--   §2.2–§2.3, pp. 1069–1070 — multi-class fluid model: subclass configurations, within-class program (6) and its value C_i, across-class program (2)
-- statement:
--   This file sets up the fluid model of a multi-class many-server queue with impatient customers (Bassamboo, Randhawa and Wu, §2).
--
--   **Classes.** There are $m$ customer classes $i = 1,\dots,m$. Class $i$ arrives at rate $\Lambda_i$, has mean service time $1/\mu_i$, and its customers abandon according to a patience distribution $F_i$ with survival function $\bar F_i = 1 - F_i$. A customer who is offered a wait $w \in [0,\infty]$ (the time it would wait before service if it were infinitely patient) incurs the average cost $\bar c_i(w)$ of (5). The **standing assumptions** are
--   $$\Lambda_i > 0,\qquad \mu_i > 0,\qquad 0 \le \bar F_i(w) \le 1,\qquad \bar F_i \text{ nonincreasing},\qquad \bar F_i(\infty) = 0 .$$
--   A separate predicate records nonnegative costs, $\bar c_i(w) \ge 0$ for all $w$.
--
--   **Subclass configurations and program (6).** A configuration of class $i$ splits the class into $J(i) \ge 1$ subclasses, each served FCFS, subclass $j$ having arrival rate $\lambda_{i,j}$, offered wait $w_{i,j} \in [0,\infty]$ and capacity $n_{i,j}$. It is feasible for (6) at capacity $n_i$ when $\lambda_{i,j} \ge 0$, $n_{i,j} \ge 0$ and
--   $$\sum_{j=1}^{J(i)} \lambda_{i,j} = \Lambda_i,\qquad \lambda_{i,j}\,\bar F_i(w_{i,j}) \le n_{i,j}\,\mu_i \ \ (j = 1,\dots,J(i)),\qquad \sum_{j=1}^{J(i)} n_{i,j} \le n_i .$$
--   Its cost rate is $\sum_j \lambda_{i,j}\,\bar c_i(w_{i,j})$, and the cost function of class $i$ is the value of (6),
--   $$C_i(n_i) = \inf\Big\{ \sum_{j=1}^{J(i)} \lambda_{i,j}\,\bar c_i(w_{i,j}) \;:\; \text{the configuration is feasible at } n_i \Big\}.$$
--
--   **Plans and program (2).** A plan assigns a capacity $n_i$ and a configuration to every class. It is feasible when $n_i \ge 0$, $\sum_i n_i \le N$ and every class configuration is feasible for (6) at $n_i$; its cost is the sum of the class cost rates. A **fluid-optimal solution** is a feasible plan of least cost among feasible plans.
--
--   These are the objects of Lemma 1 (structure of an optimal configuration of (6)), Lemma 2 (shape of $C_i$) and Proposition 1 (structure of a fluid-optimal plan).
--
--   **Formalization Note.** Offered waits are extended nonnegative reals, so $w = \infty$, the never-served subclass of p. 1070 (LCFS is $(0,\infty)$), is allowed; rates, capacities and costs are real numbers. The cost $\bar c_i$ is an arbitrary function of the offered wait: (5) defines it from $\xi_i$, $G_i$ and $F_i$, but every function of $w$ arises from (5) (take $\xi_i(x,y,w) = g(w)$), and $\bar F_i$ and $\bar c_i$ are therefore decoupled. The two-stage program (2)+(6) is encoded as one joint program over plans; a plan is optimal for it exactly when its capacities are optimal for (2) and each configuration is optimal for (6) at its capacity, whenever these optima exist. $C_i$ is a real infimum, which is meaningful (the feasible set is nonempty and the costs are bounded below) when $n_i \ge 0$ and $\bar c_i \ge 0$. The positivity of $\Lambda_i$, the bounds on $\bar F_i$, $\bar F_i(\infty)=0$ and the nonnegativity of $\lambda_{i,j}$, $n_{i,j}$ are implicit in the paper (rates, a survival function of a finite patience time, and (12)); they are written out here.
-- source:
--   Bassamboo, Randhawa & Wu, Optimally scheduling heterogeneous impatient customers, Manufacturing & Service Operations Management 25(3):1066–1080 (2023), pp. 1068–1070, §2.1–§2.3, (2)–(6)

import Mathlib

open scoped ENNReal

namespace HetImpatient.FluidSplit

/-- Primitive data of the `m` customer classes (§2.1–§2.2, pp. 1068–1070): arrival rate `Λ i`,
service rate `μ i` (mean service time `1/μ i`), patience survival function `Fbar i = 1 − F_i`
evaluated at an offered wait in `[0, ∞]`, and per-customer cost `cbar i w` of (5). -/
structure ClassData (m : ℕ) where
  Λ : Fin m → ℝ
  μ : Fin m → ℝ
  Fbar : Fin m → ℝ≥0∞ → ℝ
  cbar : Fin m → ℝ≥0∞ → ℝ

/-- Standing assumptions of §2: positive arrival and service rates, and `Fbar i` a survival
function of a finite patience time (values in `[0,1]`, nonincreasing, `0` at `w = ∞`). -/
def ClassData.Standing {m : ℕ} (D : ClassData m) : Prop :=
  ∀ i, 0 < D.Λ i ∧ 0 < D.μ i ∧ (∀ w, 0 ≤ D.Fbar i w ∧ D.Fbar i w ≤ 1) ∧
    Antitone (D.Fbar i) ∧ D.Fbar i ⊤ = 0

/-- Nonnegative per-customer costs `cbar i w ≥ 0`. -/
def ClassData.CostNonneg {m : ℕ} (D : ClassData m) : Prop :=
  ∀ i w, 0 ≤ D.cbar i w

/-- A split of one class into `J` FCFS subclasses: arrival rates `lam j = λ_{i,j}`, offered waits
`w j = w_{i,j}` and capacities `n j = n_{i,j}`. -/
structure Config where
  J : ℕ
  lam : Fin J → ℝ
  w : Fin J → ℝ≥0∞
  n : Fin J → ℝ

/-- The constraints of the within-class program (6) for class `i` at capacity `ni`:
`J(i) ≥ 1`, nonnegative rates and capacities, `∑_j λ_{i,j} = Λ_i`,
`λ_{i,j} F̄_i(w_{i,j}) ≤ n_{i,j} μ_i` for every `j`, and `∑_j n_{i,j} ≤ n_i`. -/
def ClassFeasible {m : ℕ} (D : ClassData m) (i : Fin m) (ni : ℝ) (c : Config) : Prop :=
  1 ≤ c.J ∧ (∀ j, 0 ≤ c.lam j) ∧ (∀ j, 0 ≤ c.n j) ∧
    ∑ j, c.lam j = D.Λ i ∧
    (∀ j, c.lam j * D.Fbar i (c.w j) ≤ c.n j * D.μ i) ∧
    ∑ j, c.n j ≤ ni

/-- Objective of (6): `∑_j λ_{i,j} c̄_i(w_{i,j})`. -/
def classCost {m : ℕ} (D : ClassData m) (i : Fin m) (c : Config) : ℝ :=
  ∑ j, c.lam j * D.cbar i (c.w j)

/-- The cost function `C_i(n_i)` of (6): the infimum of the objective over feasible splits. -/
noncomputable def C {m : ℕ} (D : ClassData m) (i : Fin m) (ni : ℝ) : ℝ :=
  sInf (classCost D i '' {c | ClassFeasible D i ni c})

/-- A plan for (2) with (6): a capacity `n i` for every class and a split of every class. -/
structure Plan (m : ℕ) where
  n : Fin m → ℝ
  cfg : Fin m → Config

/-- Feasibility for the joint program (2)+(6): `n_i ≥ 0`, `∑_i n_i ≤ N`, and each class split is
feasible for (6) at its capacity `n_i`. -/
def PlanFeasible {m : ℕ} (D : ClassData m) (N : ℝ) (P : Plan m) : Prop :=
  (∀ i, 0 ≤ P.n i) ∧ ∑ i, P.n i ≤ N ∧ ∀ i, ClassFeasible D i (P.n i) (P.cfg i)

/-- Total cost rate of a plan: `∑_i ∑_j λ_{i,j} c̄_i(w_{i,j})`. -/
def planCost {m : ℕ} (D : ClassData m) (P : Plan m) : ℝ :=
  ∑ i, classCost D i (P.cfg i)

/-- A fluid-optimal solution: a feasible plan of minimal total cost among feasible plans. -/
def IsFluidOptimal {m : ℕ} (D : ClassData m) (N : ℝ) (P : Plan m) : Prop :=
  PlanFeasible D N P ∧ ∀ Q, PlanFeasible D N Q → planCost D P ≤ planCost D Q

end HetImpatient.FluidSplit


