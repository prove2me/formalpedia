-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_Optima
-- name    : SingleMachineSched_AlphaJSched_Supplement_Optima
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:08:27.999285+00:00
-- url     : https://prove2.me/theorems/caa198f6-c195-41bc-8283-82541a8e6334
-- title:
--   Off-line optimal weighted completion cost and makespan
-- statement:
--   For integral processing requirements $p_j$ and releases $r_j$, write $\mathcal S$ for all feasible nonpreemptive schedules with real start times. Define
--   $$\operatorname{OPT}=\inf_{s\in\mathcal S}\sum_j w_j(s_j+p_j),\qquad C^*_{\max}=\inf\{T\ge0:\exists s\in\mathcal S,\ \forall j,\ s_j+p_j\le T\}.$$
--   These are the off-line comparators for competitive ratio and makespan. They are computed from the scheduling instance, rather than supplied as arbitrary bounds. Serial processing after the last release gives a feasible schedule. Under positive weights the cost set is bounded below by zero; makespans are explicitly nonnegative. Both infima are attained by earliest schedules for one of finitely many orders. With no jobs both values are zero.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), DOI 10.1137/S089548019936223X, pp. 165, 179 and 189 (PDF 1, 15 and 25)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_Supplement_NonpreemptiveSchedule

namespace SingleMachineSched.AlphaJSched.Supplement

/-- The off-line optimum of `1 | r_j | ∑ w_j C_j` over real start times.
On the theorem domain its objective set is nonempty and bounded below. -/
noncomputable def optValue {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) : ℝ :=
  sInf ((fun s : Fin n → ℝ => ∑ j, w j * (s j + (p j : ℝ))) ''
    {s | IsNonpreemptiveSchedule p r s})

/-- Optimal nonpreemptive makespan (§3.2, p. 179), with zero makespan for no jobs.
The explicit nonnegativity of the horizon prevents an unbounded-below empty-job infimum. -/
noncomputable def optMakespan {n : ℕ} (p r : Fin n → ℕ) : ℝ :=
  sInf {T : ℝ | 0 ≤ T ∧ ∃ s : Fin n → ℝ,
    IsNonpreemptiveSchedule p r s ∧ ∀ j, s j + (p j : ℝ) ≤ T}

end SingleMachineSched.AlphaJSched.Supplement


