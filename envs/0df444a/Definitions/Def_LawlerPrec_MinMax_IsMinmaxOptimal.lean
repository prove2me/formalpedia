-- Prove2me | Definitions.Def_LawlerPrec_MinMax_IsMinmaxOptimal
-- name    : LawlerPrec_MinMax_IsMinmaxOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:14:05.817724+00:00
-- url     : https://prove2.me/theorems/42d66af7-cab6-4f78-b9da-e97db542dbbb
-- title:
--   Minmax optimal sequence under precedence constraints
-- statement:
--   Each job $j$ of a nonempty finite job set $J$ has a processing time $a_j$ and a cost function $c_j(t)$, the cost incurred when $j$ is completed at time $t$. The machine starts at time $0$ and processes the jobs of a sequence $\pi$ one after another without idle time, so the completion time $C_j(\pi)$ of $j$ is the sum of the processing times of $j$ and of all jobs before it. The **maximum incurred cost** of $\pi$ is
--
--   $$
--   f_{\max}(\pi) \;=\; \max_{j \in J} c_j\bigl(C_j(\pi)\bigr).
--   $$
--
--   A sequence $\pi$ is **minmax optimal** if it observes the precedence constraints and
--
--   $$
--   f_{\max}(\pi) \;\le\; f_{\max}(\pi') \qquad \text{for every sequence } \pi' \text{ of } J \text{ observing the precedence constraints.}
--   $$
--
--   This is the objective of Lawler's problem: "find a sequence which will minimize the maximum of the incurred costs".
--
--   **Formalization Note** $f_{\max}$ is the published `MooreLateJobs.MaxDeferral.maxCost`, applied with Lawler's processing times $a$ (Moore's variable name for them is `t`) and Lawler's cost functions $c_j$. Moore's continuity and boundedness assumptions on deferral costs are not part of that definition and are not assumed here. Nonemptiness of $J$ is needed for the maximum to exist.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §1 Problem Formulation and §2 THEOREM ("a minmax optimal sequence, i.e. a sequence which minimizes the maximum of the incurred costs")

import Mathlib
import Definitions.Def_MooreLateJobs_MaxDeferral_maxCost
import Definitions.Def_LawlerPrec_MinMax_IsFeasible

namespace LawlerPrec.MinMax

/-- A minmax optimal sequence (Lawler 1973, §1–2, p. 544): `l` is a sequence of the nonempty job
set `J` that observes the precedence constraints `prec`, and no sequence of `J` observing them
has a smaller maximum incurred cost `max_{j ∈ J} c_j(C_j)`, where `C_j` is the completion time of
`j` with processing times `a` (machine starts at time `0`, no idle time). -/
def IsMinmaxOptimal {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (J : Finset ι) (hJ : J.Nonempty) (l : List ι) : Prop :=
  IsFeasible prec J l ∧
    ∀ l' : List ι, IsFeasible prec J l' →
      MooreLateJobs.MaxDeferral.maxCost a c J hJ l ≤ MooreLateJobs.MaxDeferral.maxCost a c J hJ l'

end LawlerPrec.MinMax


