-- Prove2me | Definitions.Def_AndOrSched_delta
-- name    : AndOrSched_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:58.335234+00:00
-- url     : https://prove2.me/theorems/47aa6bbd-3dca-4633-9842-011eefb0d2ac
-- title:
--   $\Delta$, the maximum number of OR-predecessors
-- statement:
--   $$\Delta:=\max\Bigl(1,\ \max_{b\in B}|\mathcal P(b)|\Bigr),$$
--   where $\mathcal P(b)$ is taken after removing redundant OR-arcs. The paper defines $\Delta:=\max_{b\in B}|\mathcal P(b)|$ and sets $\Delta=1$ when $\mathcal P(b)=\emptyset$ for all $b$. So $\Delta\ge1$ always.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4, "Let ∆ := maxb∈B |P(b)|"; §2, p.7, "we set ∆ = 1"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_orPred
import Definitions.Def_AndOrSched_nonRedPred
open scoped Classical NNReal

namespace AndOrSched

/-- `Δ`, the maximum number of OR-predecessors of a job in `B` after removing redundant OR-arcs
(Happach, Schulz, arXiv:2001.07011v1, §1, p.4, "Let ∆ := maxb∈B |P(b)|"), with `Δ = 1` when no job has an OR-predecessor
(§2, p.7, "In this case, we set ∆ = 1").

**Formalization Note** `Δ = max(1, max_b |𝒫(b)|)` with `𝒫(b)` the non-redundant OR-predecessors
`nonRedPred`. The `max` with `1` also covers `B = ∅` and `P(b) = ∅` for all `b`. So `Δ ≥ 1`. -/
noncomputable def delta (I : Instance) : ℕ :=
  max 1 (Finset.univ.sup fun b => (nonRedPred I b).card)

end AndOrSched


