-- Prove2me | Definitions.Def_AndOrSched_listC
-- name    : AndOrSched_listC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:04.637962+00:00
-- url     : https://prove2.me/theorems/7ffb7a7a-dfd3-4d5e-aef5-46a71e43d94a
-- title:
--   The schedule of a job order
-- statement:
--   Given an order $\prec$ of the jobs, the jobs are processed in that order without idle time from time $0$, so job $j$ completes at
--   $$C_j=\sum_{i\preceq j}p_i .$$
--
--   **Formalization Note** An order is a bijection from the jobs to positions $\{0,\dots,|N|-1\}$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.8, (3), "α Cb(β) = Σi⪯b α pi"

import Mathlib
import Definitions.Def_AndOrSched_Instance
open scoped Classical NNReal

namespace AndOrSched

/-- The schedule of a job order (Happach, Schulz, arXiv:2001.07011v1, §2, p.8, (3), "α Cb(β) = Σ_{i⪯b} α pi"): the jobs are
processed in the order `σ` without idle time from time `0`, so job `j` completes at
`Cⱼ = Σ_{i ⪯ j} pᵢ`.

**Formalization Note** An order is a bijection `σ : N ≃ Fin |N|` (position of each job), and
`i ⪯ j` is `σ i ≤ σ j`. -/
def listC (I : Instance) (σ : I.N ≃ Fin (Fintype.card I.N)) (j : I.N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => σ i ≤ σ j), (I.p i : ℝ)

end AndOrSched


