-- Prove2me | Definitions.Def_MWCSherali_cost
-- name    : MWCSherali_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:59.389655+00:00
-- url     : https://prove2.me/theorems/f0776c3f-1523-4eb9-b2e2-2115a02d3dcd
-- title:
--   Cost of a labeling of $\Delta_{k,n}$
-- statement:
--   For a weight function $w$ on $E_{k,n}$ and a labeling $P:\Delta_{k,n}\to[k+1]$, an edge $\{u,v\}$ is **cut** by $P$ if $P(u)\neq P(v)$, and
--
--   $$\operatorname{cost}(w,P)=\sum_{e=\{u,v\}\in E_{k,n}}w_e\,\mathbf 1[P(u)\neq P(v)].$$
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges

namespace MWCSherali

/-- **Cost of a labeling of `Δ_{k,n}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511
(version of Nov. 3, 2026), §2.1, p.14:
`cost(w, P) = ∑_{e = {u,v} ∈ E_{k,n}} w_e · 1[P(u) ≠ P(v)]`.

**Formalization Note.** An edge `e = {u, v}` is cut by `P` when the pair `{P u, P v}`
(`Sym2.map P e`) is not a diagonal pair. -/
def cost {k n : ℕ} (w : Sym2 (Grid k n) → ℝ) (P : Grid k n → Fin (k + 1)) : ℝ :=
  ∑ e ∈ edges k n, if (Sym2.map P e).IsDiag then 0 else w e

end MWCSherali


