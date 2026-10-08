-- Prove2me | Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum
-- name    : DeterioratingJobs_Makespan_InterchangeSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:55:08.546872+00:00
-- url     : https://prove2.me/theorems/6ad58285-49f5-4ccf-91b2-d6a2abbb1e35
-- title:
--   Lemma 1, Eq. (1) — the sum $\sum_i \mu_{\pi(i)}\prod_{r>i}\gamma_{\pi(r)}$ along a permutation
-- statement:
--   Let $N$ be a number of jobs, indexed by $I=\{1,\dots,N\}$, and let $\mu_1,\dots,\mu_N$ and $\gamma_1,\dots,\gamma_N$ be real numbers attached to the jobs. A **permutation** $\pi$ of $I$ is read as a processing order: $\pi(i)=j$ means that job $j$ is the $i$-th one processed. The sum (1) of Browne and Yechiali's Lemma 1 is
--
--   $$
--   \sum_{i=1}^{N} \mu_{\pi(i)} \prod_{r=i+1}^{N} \gamma_{\pi(r)},
--   $$
--
--   the sum over positions $i$ of the value $\mu$ of the job in position $i$, multiplied by the product of the factors $\gamma$ of all jobs processed after it. The product for the last position is empty and equals $1$.
--
--   Sums of this shape arise as the objective of every deterioration model in the paper: the expected makespan under linear deterioration is the case $\mu_i=\mathrm E(X_i)$, $\gamma_i=1+\alpha_i$.
--
--   **Formalization Note** Jobs are `Fin N` and positions are 0-based: the Lean job `i` is the paper's job $i+1$, and `π i` is the job in (0-based) position `i`. The product runs over `Finset.Ioi i`, the positions strictly after `i`. No sign condition is imposed on $\mu$ or $\gamma$ in the definition.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 495, Lemma 1, Eq. (1); the class Π of permutations, p. 495

import Mathlib

namespace DeterioratingJobs.Makespan

/-- The sum (1) of Lemma 1 (Browne–Yechiali 1990, p. 495), evaluated along the permutation `π`:
`∑_{i} μ_{π(i)} ∏_{r > i} γ_{π(r)}`. Positions are 0-based: `π i` is the job in position `i`, and
the product runs over the positions strictly after `i` (empty product `= 1` at the last position). -/
noncomputable def lemma1Sum {N : ℕ} (μ γ : Fin N → ℝ) (π : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i : Fin N, μ (π i) * ∏ r ∈ Finset.Ioi i, γ (π r)

end DeterioratingJobs.Makespan


