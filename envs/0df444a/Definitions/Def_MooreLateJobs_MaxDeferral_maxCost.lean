-- Prove2me | Definitions.Def_MooreLateJobs_MaxDeferral_maxCost
-- name    : MooreLateJobs_MaxDeferral_maxCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:34:26.938512+00:00
-- url     : https://prove2.me/theorems/adfcfe55-e7f6-4900-8581-9798616eb47e
-- title:
--   The maximum deferral cost of a schedule
-- statement:
--   Let $J$ be a nonempty finite set of jobs with processing times $t_j$ and deferral costs $P_j$, where $P_j(s)$ is the cost of completing job $j$ at time $s$. The **maximum deferral cost** incurred by a sequence $S$ is
--   $$
--   \max_{j\in J} P_j(C_j),
--   $$
--   where $C_j$ is the completion time of $j$ in $S$ (Moore 1968, p. 108).
--
--   The objective of the section is a schedule for which this quantity is minimal.
--
--   **Formalization Note** `maxCost t P J hJ l` is `Finset.sup'` over the nonempty set $J$ (the proof `hJ` of nonemptiness is an argument, so the maximum over no jobs never arises).
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 108, "Minimizing the Maximum Deferral Cost", first paragraph ("the maximum deferral cost incurred")

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace MooreLateJobs.MaxDeferral

/-- The maximum deferral cost incurred by the sequence `l` on the (nonempty) job set `J`
(p. 108): `max_{j ∈ J} P_j(C_j)`, where `C_j` is the completion time of `j` in `l`. -/
noncomputable def maxCost {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (P : ι → ℝ → ℝ)
    (J : Finset ι) (hJ : J.Nonempty) (l : List ι) : ℝ :=
  J.sup' hJ (fun j => P j (Shared.completionTime t l j))

end MooreLateJobs.MaxDeferral


