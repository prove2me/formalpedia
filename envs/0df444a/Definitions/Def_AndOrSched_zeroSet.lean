-- Prove2me | Definitions.Def_AndOrSched_zeroSet
-- name    : AndOrSched_zeroSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:16.193479+00:00
-- url     : https://prove2.me/theorems/2a4da969-c060-48e8-8dc3-95ac7fc76833
-- title:
--   The disregarded zero-time jobs $Z$
-- statement:
--   $Z$ is the least set of jobs such that a job $k$ belongs to $Z$ whenever $p_k=0$, all AND-predecessors of $k$ belong to $Z$, and either $k\in A$, or $k=b\in B$ with $\mathcal P(b)=\emptyset$ or with an OR-predecessor in $Z$. All jobs of $Z$ can complete at time $0$ in a feasible schedule.
--
--   This makes precise the paper's "otherwise such a job can be disregarded". Deleting a zero-time job $a\in\mathcal P(b)$ outright would remove a free OR-predecessor of $b$ and can raise the optimum, so instead every job that can complete at time $0$ is put into $Z$ and scheduled there, and an OR-successor of a job of $Z$ loses its OR-constraint.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6, "pj ≥ 1 for every job j ∈ N that has no predecessors (otherwise such a job can be disregarded)"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_andRel
import Definitions.Def_AndOrSched_orPred
open scoped Classical NNReal

namespace AndOrSched

/-- The set `Z` of jobs that can be "disregarded" (Happach, Schulz, arXiv:2001.07011v1, §2, p.6, "pj ≥ 1 for every job j ∈ N
that has no predecessors (otherwise such a job can be disregarded)"): the least set of jobs such
that a job `k` belongs to it whenever `p_k = 0`, all AND-predecessors of `k` belong to it, and
`k ∈ A`, or `k = b ∈ B` with `𝒫(b) = ∅` or with some OR-predecessor in it. Every job of `Z` can be
completed at time `0`.

**Formalization Note** This is a reading of the under-specified "can be disregarded": deleting a
zero-time job `a ∈ 𝒫(b)` literally would remove a cheap OR-predecessor of `b` and can raise the
optimum, so every job that can complete at time `0` is put in `Z`, and an OR-successor of a job in
`Z` loses its OR-constraint. `Z` is the intersection of all sets closed under the rule. -/
def zeroSet (I : Instance) : Set I.N :=
  {j | ∀ S : Set I.N,
    (∀ k : I.N, I.p k = 0 → (∀ i, andRel I i k → i ∈ S) →
      ((∃ a, k = Sum.inl a) ∨
        ∃ b, k = Sum.inr b ∧ (orPred I b = ∅ ∨ ∃ a ∈ orPred I b, Sum.inl a ∈ S)) → k ∈ S) →
    j ∈ S}

end AndOrSched


