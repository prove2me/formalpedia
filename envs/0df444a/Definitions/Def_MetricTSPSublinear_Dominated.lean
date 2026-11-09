-- Prove2me | Definitions.Def_MetricTSPSublinear_Dominated
-- name    : MetricTSPSublinear_Dominated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:26.576926+00:00
-- url     : https://prove2.me/theorems/53a2d396-3a05-4e31-9059-952b0c3ff94c
-- title:
--   Steiner trees dominated by the metric
-- statement:
--   A Steiner tree $F$ on $S$ is **dominated by the metric** $d$ if
--   $$d_F(u,v)\le d(u,v)\qquad\text{for all } u,v\in S,$$
--   where $d_F(u,v)$ is the sum of the edge weights on the $u$–$v$ path in $F$.
--
--   Dominated Steiner trees are exactly the trees whose dual solutions are feasible (Claim 4.1).
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MetricTSPSublinear_SteinerTree

namespace MetricTSPSublinear

/-- **A Steiner tree dominated by the metric.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §4.1, p.12 (PDF p.14): "We say a Steiner tree F spanning V is dominated by the metric if it
satisfies: d_F(u, v) ≤ d(u, v), where d_F(u, v) denotes the sum of edge weights on the path from u to v in F."

`Dominated d F` says `d_F(ι u, ι v) ≤ d u v` for all points `u, v ∈ S`.

**Formalization Note.** For `S = Finset.univ` this is the page's definition; for general `S` it is domination by the
metric induced on `S` (the page's "dominated tree C spanning S", p.17). -/
def Dominated {n : ℕ} {S : Finset (Fin n)} (d : Fin n → Fin n → ℝ) (F : SteinerTree S) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, F.pathWt (F.ι u) (F.ι v) ≤ d u v

end MetricTSPSublinear


