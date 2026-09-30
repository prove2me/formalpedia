-- Prove2me | Definitions.Def_SingleMachineSched_LPRelax_LPSchedule
-- name    : SingleMachineSched_LPRelax_LPSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:49:32.133124+00:00
-- url     : https://prove2.me/theorems/3d5f9d85-bd1a-45d7-88ee-8cced1bf7035
-- title:
--   The LP schedule (preemptive smallest-index rule), its mean busy times $M^{LP}_j$ and its slot vector $y^{LP}$
-- statement:
--   Let jobs $0, 1, \dots, n-1$ have integral processing times $p_j$ and release dates $r_j$. The **LP schedule** is the preemptive schedule that, at every point in time, processes the available (released and unfinished) job of smallest index.
--
--   Because all data are integral, every release and every completion in this schedule happens at an integer time, so the schedule is determined by which job it runs in each unit slot $[\tau, \tau + 1)$, $\tau = 0, 1, 2, \dots$. Write $\rho_j(\tau)$ for the work of job $j$ left at the start of slot $\tau$, with $\rho_j(0) = p_j$. In slot $\tau$ the machine runs the smallest index $j$ with $r_j \le \tau$ and $\rho_j(\tau) > 0$, and idles if there is none; the chosen job's remaining work drops by one.
--
--   1. The set of times at which the LP schedule processes job $j$ is
--   $$A^{LP}_j = \bigcup_{\tau \,:\, \text{job } j \text{ runs in slot } \tau} [\tau, \tau + 1),$$
--   and $M^{LP}_j$ is the mean busy time of job $j$ in it.
--   2. The **slot vector** of the LP schedule is $y^{LP}_{j\tau} = 1$ if job $j$ is processed in $[\tau, \tau+1)$ and $y^{LP}_{j\tau} = 0$ otherwise.
--
--   In the paper the jobs are indexed so that $w_1/p_1 \ge w_2/p_2 \ge \cdots \ge w_n/p_n$ with ties broken by index, and the LP schedule processes the available job of largest ratio $w_j/p_j$. Under that indexing the two rules coincide. All theorems that use the LP schedule assume that indexing.
--
--   **Formalization Note** The sortedness of $w_j/p_j$ is not part of the definition; it is a hypothesis of every theorem about the LP schedule. The definition is by recursion on the slot index. That $A^{LP}$ is a preemptive schedule, and that $y^{LP}$ is feasible for (D), are theorems, not part of the definition.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 169 (LP schedule), p. 170 (slot vector $y^{LP}$), p. 171 (mean busy time)

import Mathlib
import Definitions.Def_SingleMachineSched_Shared_PreemptiveSchedule

namespace SingleMachineSched.LPRelax

/-- The job the smallest-index preemptive rule runs in the unit slot `[τ, τ + 1)` when `rem j`
units of work of job `j` are left: the smallest index among released, unfinished jobs, or
`none` (idle) if there is none. -/
def lpPick {n : ℕ} (r : Fin n → ℕ) (τ : ℕ) (rem : Fin n → ℕ) : Option (Fin n) :=
  if h : (Finset.univ.filter (fun j => r j ≤ τ ∧ 0 < rem j)).Nonempty then
    some ((Finset.univ.filter (fun j => r j ≤ τ ∧ 0 < rem j)).min' h)
  else none

/-- Work left of each job at the start of slot `τ` in the LP schedule. -/
def lpRemaining {n : ℕ} (p r : Fin n → ℕ) : ℕ → Fin n → ℕ
  | 0 => p
  | τ + 1 => fun j =>
      if lpPick r τ (lpRemaining p r τ) = some j then lpRemaining p r τ j - 1
      else lpRemaining p r τ j

/-- The job processed in slot `[τ, τ + 1)` by the LP schedule (`none` = machine idle). -/
def lpRun {n : ℕ} (p r : Fin n → ℕ) (τ : ℕ) : Option (Fin n) :=
  lpPick r τ (lpRemaining p r τ)

/-- The set of times at which the LP schedule processes job `j`. -/
def lpSet {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : Set ℝ :=
  ⋃ (τ : ℕ) (_ : lpRun p r τ = some j), Set.Ico (τ : ℝ) (τ + 1)

/-- `M^LP_j`, the mean busy time of job `j` in the LP schedule. -/
noncomputable def mLP {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) : ℝ :=
  Shared.meanBusyTime p (lpSet p r) j

/-- `y^LP_{jτ}`: `1` if the LP schedule processes `j` in `[τ, τ + 1)`, `0` otherwise (p. 170). -/
def yLP {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) (τ : ℕ) : ℝ :=
  if lpRun p r τ = some j then 1 else 0

end SingleMachineSched.LPRelax


