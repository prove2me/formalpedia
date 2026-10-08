-- Prove2me | Definitions.Def_DeterioratingJobs_Weighted_Model
-- name    : DeterioratingJobs_Weighted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:18.363962+00:00
-- url     : https://prove2.me/theorems/b4627d3f-ba1f-4ebb-a316-d5c704e7e3b7
-- title:
--   Sections 1–2 — linear deterioration, completion times, and weighted completion cost
-- statement:
--   There are $N$ jobs, indexed $1,\ldots,N$, available at time zero for processing without preemption or idle time on one processor. A schedule $\pi$ is a permutation: $\pi(k)$ is the job in position $k$. Job $i$ has a random initial processing requirement $X_i$ and a deterministic growth rate $\alpha_i$. If it starts at time $t$, its actual processing time is
--   $$
--   Y_i(t)=X_i+\alpha_i t.
--   $$
--   The completion times are defined from this processing rule: $S_0(\pi)=0$ and $S_{k+1}(\pi)=S_k(\pi)+Y_{\pi(k+1)}(S_k(\pi))$. With waiting cost rate $c_i$ for job $i$, the total weighted completion cost is
--   $$
--   C(\pi)=\sum_{k=1}^{N}c_{\pi(k)}S_k(\pi).
--   $$
--   The recursion is the model from which the later closed formulas and scheduling results are derived.
--
--   **Formalization Note** Job and position indices are zero-based in Lean, so the job at position $k$ finishes at $S_{k+1}$. At steps beyond the $N$th job, $S$ stays at $S_N$. The parameter functions and rates are unrestricted here; individual theorems state integrability and positivity where needed. This duplicates the contemporaneous Makespan mission's model because its draft definition cannot be imported.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), pp. 495–497, Sections 1–2, Y_i(t), Eq. (2), and the sentence before Eq. (8); https://doi.org/10.1287/opre.38.3.495

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Weighted

open MeasureTheory

/-- Sum of each job's waiting cost rate times its completion time (p. 497).
The job at zero-based position `k` is `π k` and finishes at `S_(k+1)`. -/
def totalCost {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ)
    (α c : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (ω : Ω) : ℝ :=
  ∑ k : Fin N, c (π k) * DeterioratingJobs.Makespan.completionTime X α π (k.val + 1) ω

end DeterioratingJobs.Weighted


