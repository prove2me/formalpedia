-- Prove2me | Definitions.Def_MetricMSO_gcw
-- name    : MetricMSO_gcw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:14.695435+00:00
-- url     : https://prove2.me/theorems/65cf24fb-8702-40fe-9827-374bca506982
-- title:
--   Cliquewidth $\mathrm{cw}(G)$ and geodesic cliquewidth $\mathrm{gcw}(G)$
-- statement:
--   The **cliquewidth** $\mathrm{cw}(G)$ is the least $k$ such that $G$ is the value of a $k$-expression, disregarding the labels at the end. The **geodesic cliquewidth** is
--   $$\mathrm{gcw}(G):=\mathrm{cw}(G)+\mathrm{cbl}(G).$$
--
--   This is the parameter of part (ii) of the goal.
--
--   **Formalization Note** $k$-expressions are the published `KExpr` and `HasKExpr` (create, $\eta_{i,j}$ with $i\ne j$, $\rho_{i\to j}$, disjoint union). A graph with no vertex has no $k$-expression, and the infimum of the empty set gives $\mathrm{cw}=0$ there.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.5, Definition 2.4, p.15 (PDF 17)

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_MetricMSO_cbl

namespace MetricMSO

open ApproxCliqueWidth.Certificate (HasKExpr)

/-- **Cliquewidth `cw(G)`.**

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.5, p.15 (PDF 17):
"With a k-expression, we construct a vertex-labeled graph using labels from [k] and four operations
… The cliquewidth cw(G) is the least k for which we can construct G in this way, where we disregard
the labels at the end of the construction."

`cw G` is the least `k` such that `G` is isomorphic to the value of a `k`-expression (published
`ApproxCliqueWidth.Certificate.HasKExpr`).

**Formalization Note** A graph with no vertex has no `k`-expression, so `sInf ∅ = 0` gives
`cw = 0` there. -/
noncomputable def cw {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k | HasKExpr G k}

/-- **Geodesic cliquewidth**, Definition 2.4, p.15 (PDF 17): "We define the geodesic cliquewidth of a
graph G by gcw(G) := cw(G) + cbl(G)." -/
noncomputable def gcw {V : Type} (G : SimpleGraph V) : ℕ :=
  cw G + cbl G

end MetricMSO


