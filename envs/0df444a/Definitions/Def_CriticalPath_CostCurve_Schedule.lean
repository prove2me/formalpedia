-- Prove2me | Definitions.Def_CriticalPath_CostCurve_Schedule
-- name    : CriticalPath_CostCurve_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:30:29.072382+00:00
-- url     : https://prove2.me/theorems/2db14391-ca87-4fef-b885-706419447ebd
-- title:
--   Schedules for a completion time $\lambda$: constraints (5), (8), (9); their costs; feasible $\lambda$; minimum cost schedules
-- statement:
--   Fix a project network with jobs $P$ and job data $d, D, a, b$. For a real number $\lambda$, a **schedule for $\lambda$** is a pair $(y,t)$ of job durations $y = (y_{ij})$ and event times $t = (t_0,\dots,t_n)$ satisfying the constraints of Kelley and Walker's linear program:
--
--   $$
--   \text{(5)}\ \ d_{ij} \le y_{ij} \le D_{ij},\qquad \text{(8)}\ \ y_{ij} \le t_j - t_i \qquad \text{for all } (i,j) \in P,\qquad \text{(9)}\ \ t_0 = 0,\ \ t_n = \lambda.
--   $$
--
--   From this we define:
--
--   1. the **cost set** of $\lambda$: the set of project costs (7) of all schedules for $\lambda$;
--   2. the set $\Lambda$ of **feasible completion times**: the $\lambda$ for which some schedule exists;
--   3. a **minimum cost schedule for $\lambda$**: a schedule for $\lambda$ whose cost (7) is at most the cost of every schedule for $\lambda$.
--
--   The least element of the cost set, for $\lambda \in \Lambda$, is the value of the linear program "minimize (7) subject to (5), (8), (9)", i.e. the project cost curve at $\lambda$.
--
--   **Formalization Note** The paper's $\lambda$ is written `lam` (`λ` is reserved in Lean). The event times $t$ are otherwise unconstrained, as in the paper.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, the linear program: minimize (7) subject to (5), (8), (9)

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_JobData

namespace CriticalPath.CostCurve

variable {n : ℕ} {N : ProjectNetwork n}

/-- A schedule for the completion time `lam` (the paper's `λ`), Kelley–Walker (1959), p. 165:
durations `y` and event times `t` satisfying
(5) `dᵢⱼ ≤ yᵢⱼ ≤ Dᵢⱼ` for `(i, j) ∈ P`, (8) `yᵢⱼ ≤ tⱼ − tᵢ` for `(i, j) ∈ P`, and
(9) `t₀ = 0`, `tₙ = λ`. -/
def IsSchedule (J : JobData N) (lam : ℝ) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n + 1) → ℝ) : Prop :=
  (∀ e ∈ N.P, J.d e.1 e.2 ≤ y e.1 e.2 ∧ y e.1 e.2 ≤ J.D e.1 e.2) ∧
  (∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1) ∧
  t 0 = 0 ∧ t (Fin.last n) = lam

/-- The costs (7) of all schedules for `lam`: the objective values of the linear program
"minimize (7) subject to (5), (8), (9)". -/
def costSet (J : JobData N) (lam : ℝ) : Set ℝ :=
  {c | ∃ y t, IsSchedule J lam y t ∧ c = projectCost J y}

/-- The feasible completion times `Λ`: the `lam` for which some schedule exists. -/
def feasibleDurations (J : JobData N) : Set ℝ :=
  {lam | ∃ y t, IsSchedule J lam y t}

/-- A minimum cost schedule for `lam`: a schedule whose cost (7) is no larger than the cost of
any other schedule for `lam`. -/
def IsOptimalSchedule (J : JobData N) (lam : ℝ) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n + 1) → ℝ) : Prop :=
  IsSchedule J lam y t ∧ ∀ y' t', IsSchedule J lam y' t' → projectCost J y ≤ projectCost J y'

end CriticalPath.CostCurve


