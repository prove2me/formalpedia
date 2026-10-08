-- Prove2me | Definitions.Def_LawlerPrec_MinMax_IsLawlerSequence
-- name    : LawlerPrec_MinMax_IsLawlerSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:14:11.643136+00:00
-- url     : https://prove2.me/theorems/1cd46c0a-afe7-4813-8cbb-ef371f0e3c80
-- title:
--   Sequences produced by Lawler's backward rule (place last a least-cost eligible job)
-- statement:
--   Lawler's algorithm builds a sequence from the last position to the first. With $P$ the set of jobs not yet placed, it chooses a job $k \in S(P)$ (a job of $P$ required to precede no other job of $P$) whose cost at time $T_P = \sum_{j \in P} a_j$ is least among $S(P)$, places $k$ in the latest open position, removes it from $P$, and repeats. Ties may be broken arbitrarily.
--
--   A sequence $\pi = (\pi_1, \dots, \pi_n)$ is **produced by the rule** if for every position $m$, with $P_m = \{\pi_1, \dots, \pi_m\}$ the jobs not yet placed when position $m$ is filled and $T_m = a_{\pi_1} + \dots + a_{\pi_m}$ their total processing time (the completion time of position $m$):
--
--   1. $\pi_m \in S(P_m)$, and
--   2. $$c_{\pi_m}(T_m) \;\le\; c_j(T_m) \qquad \text{for every } j \in S(P_m).$$
--
--   Every sequence the procedure can produce, under any tie-breaking, satisfies this property, and every sequence satisfying it can be produced.
--
--   **Formalization Note** Positions are 0-based: position `m` holds `l[m]`, `P = (l.take (m + 1)).toFinset`, and $T_m$ is `MooreLateJobs.Shared.completionAt a l m`. The rule is a property of a finished sequence, not a deterministic function with a hidden tie-break. Precedence feasibility is not part of the definition; it is a consequence, stated in the goal theorem.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 545, §3 Sequencing Algorithm, first paragraph (and the worked example, second to fifth paragraphs)

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_lastEligible

namespace LawlerPrec.MinMax

/-- The sequence `l` can be produced by Lawler's backward rule (§3 Sequencing Algorithm, p. 545),
with ties broken arbitrarily. The rule fills the positions from last to first; when the
(0-based) position `m` is filled, the jobs not yet placed are `P = {l[0], …, l[m]}`, and the job
placed there completes at `T_P = completionAt a l m`, the sum of the processing times of `P`.
The rule requires, for every position `m`:
1. `l[m]` is in `S(P) = lastEligible prec P`: it is not required to precede any other job of `P`;
2. `l[m]` minimizes `c_j(T_P)` over `S(P)`: `c_{l[m]}(T_P) ≤ c_j(T_P)` for every `j ∈ S(P)`. -/
def IsLawlerSequence {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (c : ι → ℝ → ℝ)
    (prec : ι → ι → Prop) (l : List ι) : Prop :=
  ∀ (m : ℕ) (hm : m < l.length),
    l[m] ∈ lastEligible prec (l.take (m + 1)).toFinset ∧
    ∀ j ∈ lastEligible prec (l.take (m + 1)).toFinset,
      c l[m] (MooreLateJobs.Shared.completionAt a l m) ≤
        c j (MooreLateJobs.Shared.completionAt a l m)

end LawlerPrec.MinMax


