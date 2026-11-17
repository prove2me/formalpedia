-- Prove2me | Definitions.Def_PolytopeSchedPF_Supplement_IsGraphScheduling
-- name    : PolytopeSchedPF_Supplement_IsGraphScheduling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:20:26.881429+00:00
-- url     : https://prove2.me/theorems/eab01f22-b21a-4426-adf6-c9c1d7362b04
-- title:
--   Graph scheduling instances (§4.5)
-- statement:
--   In **graph scheduling** we are given a loopless multigraph $G=(V,E)$; every vertex is a processor that works on at most one job at a time and every edge is a job that must be processed on both its endpoints simultaneously. The jobs processed at any time form a matching, and by time-sharing the rate polytope is the **matching polytope** $P_G$, the convex hull of the incidence vectors of matchings of $G$.
--
--   A rate polytope $P$ on $n$ jobs is a graph-scheduling instance if $P=P_G$ for some loopless multigraph $G$ on a finite vertex set with edge set $\{1,\dots,n\}$.
--
--   This is the class of instances in the randomized lower bound (Theorem 1.5).
--
--   **Formalization Note** The multigraph, the loopless condition and $P_G$ are the published `CombOpt.MatchingPolytope` definitions (parallel edges allowed). The vertex set is `Fin m`, which covers every finite vertex set up to relabeling. That $P_G$ has a description $\{y\ge0: By\le\mathbf 1\}$ (Edmonds' matching polytope theorem, displayed on p.24) is not assumed: only the equality of rate sets is required.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §4.5, p.24 (PDF p.26), graph scheduling and P_G

import Mathlib
import Definitions.Def_PolytopeSchedPF_RatePolytope
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope

namespace PolytopeSchedPF

namespace Supplement

/-- **Graph scheduling instance** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §4.5, p.24).
We are given a loopless multigraph `G = (V, E)` whose edges are the jobs; the rate polytope is the
matching polytope `P_G`, the convex hull of the incidence vectors of matchings of `G`.
`IsGraphScheduling P` says that the rate polytope of `P` is `P_G` for some loopless multigraph on a
finite vertex set `Fin m` with edge set `Fin n`.

**Formalization Note** The graph is the published `CombOpt.MatchingPolytope.Graph` (parallel edges
allowed) with `IsLoopless`, and `P_G` is the published `matchingPolytope`. That `P_G` has a B-form
(so that `P` exists) is Edmonds' matching polytope theorem, displayed on p.24; it is not assumed,
only `P.rates = P_G` is required. Every finite vertex set is equivalent to some `Fin m`. -/
def IsGraphScheduling {n D : ℕ} (P : RatePolytope n D) : Prop :=
  ∃ (m : ℕ) (G : CombOpt.MatchingPolytope.Graph (Fin m) (Fin n)),
    G.IsLoopless ∧ P.rates = G.matchingPolytope

end Supplement

end PolytopeSchedPF


