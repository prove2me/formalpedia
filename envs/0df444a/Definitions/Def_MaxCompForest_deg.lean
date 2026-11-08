-- Prove2me | Definitions.Def_MaxCompForest_deg
-- name    : MaxCompForest_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:17.9594+00:00
-- url     : https://prove2.me/theorems/e9b7e962-393b-474b-83d8-eb338f3bee84
-- title:
--   Weighted degree $d_v$ of a labelled multigraph
-- statement:
--   For a finite labelled graph $G=(V,E)$ with positive conductances $c_e$, the **weighted degree** of a vertex $v$ is
--   $$
--   d_v=\sum_{e\ni v} c_e ,
--   $$
--   the total conductance of the labelled edges incident to $v$. Parallel labels each count once; there are no loops.
--
--   The matrix $D=\mathrm{diag}(d_v)$ enters the normalized Laplacian, and after a contraction the degrees are recomputed in the quotient.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.2, p.17

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The weighted degree** `d_v = ∑_{uv ∈ E} c_{uv}`, the total conductance of the labelled edges
incident to `v`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.2 (and p.17: "the quotient's current weighted degrees").

**Formalization Note.** The graph is the published `WGraph` (no loops, parallel labels allowed), so
each labelled edge at `v` counts once. -/
def deg (G : WGraph V E) (v : V) : ℝ :=
  ∑ e, if G.head e = v ∨ G.tail e = v then G.w e else 0

end MaxCompForest


