-- Prove2me | Definitions.Def_BakerScudder1990_Tolerance_Instance
-- name    : BakerScudder1990_Tolerance_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:49:39.577425+00:00
-- url     : https://prove2.me/theorems/725575af-cc95-48e6-9713-2ef88dac2fb6
-- title:
--   Single-machine common-due-date instance with due-date tolerances: completion times, penalty $f(d)$, least optimal due date (pp. 23, 29–30, 34)
-- statement:
--   This definition fixes the single-machine earliness/tardiness model with a **common due date** and **due-date tolerances** of Baker and Scudder, for one fixed job sequence.
--
--   There are $n$ jobs, processed on one machine in a fixed order, one after another, starting at time $0$ and without inserted idle time. The job in position $j$ has
--
--   1. a processing time $p_j$,
--   2. tolerances $u_j \ge 0$ and $v_j \ge 0$: the job avoids every penalty when it completes in the window $[d-u_j,\ d+v_j]$ around the common due date $d$,
--   3. a unit earliness penalty $\alpha_j > 0$ and a unit tardiness penalty $\beta_j > 0$.
--
--   The tolerances are required to be small relative to the processing times: for every pair of distinct jobs $i \ne j$,
--
--   $$
--   p_j - v_j - u_i > 0 ,
--   $$
--
--   so that at most one job can avoid penalty costs. The completion time of the job in position $j$ is $C_j = \sum_{i \le j} p_i$. Earliness and tardiness are measured from the ends of the tolerance window,
--
--   $$
--   E_j = (d - C_j - u_j)^+, \qquad T_j = (C_j - d - v_j)^+, \qquad f(d) = \sum_{j=1}^{n} \bigl(\alpha_j E_j + \beta_j T_j\bigr).
--   $$
--
--   A due date $d \in \mathbb R$ is **optimal** if $f(d) \le f(d')$ for every $d' \in \mathbb R$, and it is the **least optimal due date** if it is optimal and no smaller due date is optimal (the paper minimizes $d$ as a secondary criterion when there are alternative optima).
--
--   This is the model in which Properties III(G) and IV(G) of the paper are stated; every theorem of the mission is about an instance of this structure.
--
--   **Formalization Note** Jobs are indexed by their 0-based position $j \in \{0,\dots,n-1\}$ (`Fin n`); the paper's job $j$ is position $j-1$. The sequence starts at time $0$ and the due date $d$ is the decision variable, as in the paper's Appendix ("we consider the effect of increasing the due date"); only $d$ minus the start time matters, so this loses no generality for the unrestricted problem. All data are real numbers. The tolerance condition is imposed only for distinct jobs $i \ne j$ (the paper writes "for all pairs of jobs $(i,j)$", glossed as "at most one job can avoid penalty costs"); this is the weaker hypothesis. Positivity of $p_j$ is not a separate field: for $n \ge 2$ it follows from the tolerance condition, and no statement of the mission needs it for $n = 1$. $(x)^+$ is written `max 0 x`.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 23 (generic E/T model, α_j > 0, β_j > 0), pp. 29–30 (Due Date Tolerances: window [d − u_j, d + v_j], E_j, T_j, f(S), tolerance condition p_j − v_j − u_i > 0), p. 34 (secondary criterion: minimize d among alternative optima)

import Mathlib

namespace BakerScudder1990.Tolerance

/-- A single-machine earliness/tardiness instance with a common due date and due-date
tolerances, for a **fixed job sequence** (Baker and Scudder, Oper. Res. 38 (1990), p. 23 and
pp. 29–30). Jobs are indexed by their 0-based position `j : Fin n` in the sequence (the paper's
job `j + 1`). Job `j` has processing time `p j`, tolerances `u j` (before the due date) and
`v j` (after it), unit earliness penalty `α j > 0` and unit tardiness penalty `β j > 0`
(p. 23); the tolerances are nonnegative, so the penalty-free window `[d - u j, d + v j]` is an
interval (p. 29). The tolerance condition `p_j - v_j - u_i > 0` (p. 30, "at most one job can
avoid penalty costs") is imposed for distinct jobs `i ≠ j`. -/
structure Instance (n : ℕ) where
  /-- processing times `p_j` -/
  p : Fin n → ℝ
  /-- tolerance before the due date, `u_j` -/
  u : Fin n → ℝ
  /-- tolerance after the due date, `v_j` -/
  v : Fin n → ℝ
  /-- unit earliness penalties `α_j` -/
  α : Fin n → ℝ
  /-- unit tardiness penalties `β_j` -/
  β : Fin n → ℝ
  hα : ∀ j, 0 < α j
  hβ : ∀ j, 0 < β j
  hu : ∀ j, 0 ≤ u j
  hv : ∀ j, 0 ≤ v j
  /-- tolerance condition `p_j - v_j - u_i > 0` for distinct jobs `i ≠ j` (p. 30) -/
  htol : ∀ i j, i ≠ j → u i + v j < p j

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Completion time of the job in position `j` when the sequence is processed from time `0`
without inserted idle time: `C_j = ∑_{i ≤ j} p_i`. -/
def C (j : Fin n) : ℝ := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ j), I.p i

/-- Earliness of job `j` measured from the end of its tolerance window, for due date `d`:
`E_j = (d - C_j - u_j)^+` (p. 30). -/
def earliness (d : ℝ) (j : Fin n) : ℝ := max 0 (d - I.C j - I.u j)

/-- Tardiness of job `j` measured from the end of its tolerance window, for due date `d`:
`T_j = (C_j - d - v_j)^+` (p. 30). -/
def tardiness (d : ℝ) (j : Fin n) : ℝ := max 0 (I.C j - d - I.v j)

/-- Total penalty `f = ∑_j (α_j E_j + β_j T_j)` as a function of the common due date `d`
(p. 30). -/
def cost (d : ℝ) : ℝ := ∑ j, (I.α j * I.earliness d j + I.β j * I.tardiness d j)

/-- `d` is an optimal due date for the fixed sequence: it minimizes the total penalty over all
real due dates. -/
def IsOptimalDueDate (d : ℝ) : Prop := ∀ d' : ℝ, I.cost d ≤ I.cost d'

/-- `d` is the least optimal due date: optimal, and no smaller due date is optimal (the paper's
secondary criterion "minimize d … when there are alternative optima", p. 34). -/
def IsLeastOptimalDueDate (d : ℝ) : Prop :=
  I.IsOptimalDueDate d ∧ ∀ d' : ℝ, I.IsOptimalDueDate d' → d ≤ d'

end Instance

end BakerScudder1990.Tolerance


