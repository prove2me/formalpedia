-- Prove2me | Definitions.Def_CriticalPath_CostCurve_JobData
-- name    : CriticalPath_CostCurve_JobData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:29:49.109962+00:00
-- url     : https://prove2.me/theorems/aa5a23aa-b9be-4b88-9f74-0f99d230df5f
-- title:
--   Job data: crash and normal durations $0 \le d_{ij} \le D_{ij}$, linear job costs $a_{ij}y_{ij}+b_{ij}$, and the project cost (7)
-- statement:
--   For a project network with jobs $P$, **job data** assign to every job $(i,j) \in P$
--
--   1. a crash duration $d_{ij}$ and a normal duration $D_{ij}$ with $0 \le d_{ij} \le D_{ij}$, so that the admissible durations are those of (5): $0 \le d_{ij} \le y_{ij} \le D_{ij}$;
--   2. a linear job cost (6), $\text{Cost of Job }(i,j) = a_{ij} y_{ij} + b_{ij}$, with $a_{ij} \le 0$ and $b_{ij} \ge 0$.
--
--   The **project (direct) cost** (7) of durations $y$ is the sum of the job costs,
--
--   $$
--   \text{Project (Direct) Cost} = \sum_{(i,j) \in P} \left(a_{ij} y_{ij} + b_{ij}\right).
--   $$
--
--   The sign condition $a_{ij} \le 0$ expresses that expediting a job (shortening its duration) never lowers its cost.
--
--   **Formalization Note** The data are functions `Fin (n+1) → Fin (n+1) → ℝ`; only their values on $P$ are constrained and read.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 164, Part I §3 The Project Cost Function, Job Cost and Minimum Project Costs, displays (5), (6), (7)

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork

namespace CriticalPath.CostCurve

variable {n : ℕ}

/-- Job data of Kelley–Walker (1959), §3, p. 164: for every job `(i, j) ∈ P` a crash duration
`dᵢⱼ` and a normal duration `Dᵢⱼ` with `0 ≤ dᵢⱼ ≤ Dᵢⱼ` (the constant part of (5)), and a linear
job cost `aᵢⱼ yᵢⱼ + bᵢⱼ` with `aᵢⱼ ≤ 0`, `bᵢⱼ ≥ 0` ((6)). Values off `P` are never read. -/
structure JobData (N : ProjectNetwork n) where
  /-- Crash durations `dᵢⱼ`. -/
  d : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Normal durations `Dᵢⱼ`. -/
  D : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Slopes `aᵢⱼ` of the linear job costs. -/
  a : Fin (n + 1) → Fin (n + 1) → ℝ
  /-- Intercepts `bᵢⱼ` of the linear job costs. -/
  b : Fin (n + 1) → Fin (n + 1) → ℝ
  crash_nonneg : ∀ e ∈ N.P, 0 ≤ d e.1 e.2
  crash_le_normal : ∀ e ∈ N.P, d e.1 e.2 ≤ D e.1 e.2
  slope_nonpos : ∀ e ∈ N.P, a e.1 e.2 ≤ 0
  intercept_nonneg : ∀ e ∈ N.P, 0 ≤ b e.1 e.2

/-- Project (direct) cost (7), p. 164: `∑_{(i,j) ∈ P} (aᵢⱼ yᵢⱼ + bᵢⱼ)`. -/
def projectCost {N : ProjectNetwork n} (J : JobData N) (y : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ e ∈ N.P, (J.a e.1 e.2 * y e.1 e.2 + J.b e.1 e.2)

end CriticalPath.CostCurve


