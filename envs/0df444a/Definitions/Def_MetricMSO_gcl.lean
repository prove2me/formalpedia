-- Prove2me | Definitions.Def_MetricMSO_gcl
-- name    : MetricMSO_gcl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:12.030071+00:00
-- url     : https://prove2.me/theorems/d7a45559-117e-4786-99e5-4daf9717abae
-- title:
--   The geodesic-cycle length $\mathrm{gcl}(G)$
-- statement:
--   $\mathrm{gcl}(G)$ is the maximum length of a geodesic cycle of $G$, with $\mathrm{gcl}(G)=0$ when $G$ is a forest.
--
--   **Formalization Note** A supremum over the vertex sets inducing a geodesic cycle. The set is bounded by $|V(G)|$, and the empty supremum is $0$, the page's value on forests.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.3, p.14 (PDF 16)

import Mathlib
import Definitions.Def_MetricMSO_EqGC

namespace MetricMSO

/-- **The geodesic-cycle length `gcl(G)`.**

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.3, p.14 (PDF 16):
"We write gcl(G) for the maximum length of a geodesic cycle in G, with gcl(G) = 0 when G is a
forest."

`gcl G` is the largest `|C|` over the vertex sets `C` with `G[C]` a geodesic cycle (a cycle has as
many edges as vertices), and `0` if there is none.

**Formalization Note** `sSup` on `ℕ`; the set is bounded by `|V(G)|`, and `sSup ∅ = 0` gives the
value `0` on forests. A geodesic cycle is induced, so it is determined by its vertex set. -/
noncomputable def gcl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ C : Finset V, IsGeodesicCycleSet G C ∧ C.card = k}

end MetricMSO


