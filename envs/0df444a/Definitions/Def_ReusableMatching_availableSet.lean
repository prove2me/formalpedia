-- Prove2me | Definitions.Def_ReusableMatching_availableSet
-- name    : ReusableMatching_availableSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:17.905386+00:00
-- url     : https://prove2.me/theorems/d6ee64d2-a732-4cc5-ae0a-c4e4b11575e3
-- title:
--   The set $S_t$ of resources available at arrival $t$
-- statement:
--   In the run of Periodic Reranking with seed vector $Y$, the set $S_t$ consists of the resources available at arrival $t$, before $t$ is matched: those not matched to any arrival $s$ with $t-d<s<t$.
--
--   For the two-seed runs of the analysis, $S_t(y^1,y^2)$ is this set in the run whose seed vector has $y^1$ and $y^2$ in the two coordinates of resource $i$ for periods $k(j)-1$ and $k(j)$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.9 ("Let S_t(y¹,y²) denote the set of resources available at arrival t ∈ U in PR(y¹,y²)")

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **The set `S_t` of resources available at arrival `t`** in the run of Periodic Reranking with
seed vector `Y` (arXiv:2110.07084v2, p.9: "Let `S_t(y¹, y²)` denote the set of resources available
at arrival `t ∈ U` in `PR(y¹, y²)`"): the resources not matched to any arrival `s` with
`t − d < s < t`, before the decision at `t`.

**Formalization Note.** Every resource of `V` is counted, neighbour of `t` or not; the paper's
`S_t(y¹, y²)` is `availableSet I β (twoSeed I Y i j y¹ y²) t`. -/
noncomputable def availableSet {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => IsAvailable I (assignment I β Y t) v t)

end ReusableMatching


