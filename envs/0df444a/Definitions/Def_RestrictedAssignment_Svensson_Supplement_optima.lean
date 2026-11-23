-- Prove2me | Definitions.Def_RestrictedAssignment_Svensson_Supplement_optima
-- name    : RestrictedAssignment_Svensson_Supplement_optima
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:56:31.359147+00:00
-- url     : https://prove2.me/theorems/2a364d0d-795e-4513-bc30-a32cad133d44
-- title:
--   Attained scheduling and configuration-LP optima
-- statement:
--   Let $J,M$ be finite job and machine sets, with nonnegative sizes $p_j$ and allowed machines $\Gamma(j)$. For each eligible schedule $\sigma:J\to M$, set its makespan to the maximum of zero and the machine loads. The scheduling optimum is the attained minimum over the finite set of these makespans:
--   $$\mathrm{OPT}=\min_{\sigma:\,\forall j,\ \sigma(j)\in\Gamma(j)}\max\bigl(\{0\}\cup\{\sum_{\sigma(j)=i}p_j:i\in M\}\bigr).$$
--   The LP optimum is the minimum nonnegative feasible target. It is represented as a finite minimum over feasible subset-sums of processing times. Every change of the configuration sets occurs at such a sum, and the empty subset supplies zero. Consequently this finite minimum has the same value as the least feasible target and includes attainment.
--
--   These objects allow estimation to refer to the actual optimum without assuming its value. Both minima return an optional real number: absence means infeasibility, while an empty-job instance has value zero, including when there are no machines. No empty real infimum or unbounded real supremum is used. The functions are intended for nonnegative sizes, as in the source model.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, pp. 1, 3, scheduling objective and Sect. 2 (OPT_LP)

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP

namespace RestrictedAssignment.Svensson.Supplement

open Finset Classical

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

/-- Exact maximum of the machine loads, including zero so that the empty-machine
empty-job instance has makespan zero. Used only with nonnegative sizes. -/
noncomputable def makespan (p : J → ℝ) (σ : J → M) : ℝ :=
  (insert 0 (Finset.univ.image (schedLoad p σ))).max' (by simp)

/-- All total schedules that respect eligibility, not arbitrary partial schedules. -/
def eligibleSchedules (Γ : J → Finset M) : Finset (J → M) :=
  Finset.univ.filter (fun σ => ∀ j, σ j ∈ Γ j)

/-- The actual finite set of attainable makespans. -/
noncomputable def scheduleValues (Γ : J → Finset M) (p : J → ℝ) : Finset ℝ :=
  (eligibleSchedules Γ).image (makespan p)

/-- The attained minimum; `none` means there is no eligible schedule.
In particular, an infeasible instance is not assigned the real number zero. -/
noncomputable def optimalMakespan (Γ : J → Finset M) (p : J → ℝ) : Option ℝ :=
  if h : (scheduleValues Γ p).Nonempty then some ((scheduleValues Γ p).min' h)
  else none

/-- With finitely many configurations, feasibility can first appear only at zero
or at a subset-sum of processing times. The empty subset supplies zero. -/
noncomputable def feasibleBreakpoints (Γ : J → Finset M) (p : J → ℝ) : Finset ℝ :=
  ((Finset.univ : Finset (Finset J)).image (fun C => ∑ j ∈ C, p j)).filter
    (fun T => 0 ≤ T ∧ CLPFeasible Γ p T)

/-- The least feasible nonnegative target, attained at a subset-sum breakpoint;
`none` means there is no feasible target. For nonnegative sizes every change in
`configs` occurs at a subset sum, so this is the source's OPT_LP, with attainment
built into the finite minimum rather than assumed in a theorem hypothesis. -/
noncomputable def optimalLP (Γ : J → Finset M) (p : J → ℝ) : Option ℝ :=
  if h : (feasibleBreakpoints Γ p).Nonempty then some ((feasibleBreakpoints Γ p).min' h)
  else none

end RestrictedAssignment.Svensson.Supplement


