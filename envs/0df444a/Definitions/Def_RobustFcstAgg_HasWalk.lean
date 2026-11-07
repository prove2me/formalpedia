-- Prove2me | Definitions.Def_RobustFcstAgg_HasWalk
-- name    : RobustFcstAgg_HasWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:41:08.042381+00:00
-- url     : https://prove2.me/theorems/b53e8c3c-dc3d-4eca-9619-6db1ddb89336
-- title:
--   Walks of length $k$ on $\mathcal Q\cup\{Y\}$
-- statement:
--   A graph on $\mathcal Q\cup\{Y\}$ is given by the out-neighbour set of each query. This predicate says that a directed walk with exactly $k$ edges starts at a given vertex. The vertex $Y$ has no out-edges.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.2, p.6

import Mathlib

namespace RobustFcstAgg

/-- **Walks of a DAG on `𝒬 ∪ {Y}`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.2, p.6. `HasWalk out v k` says that a directed walk with
exactly `k` edges starts at the vertex `v`; `out j` is the out-neighbour set of `Q j`, and the vertex `none` (`Y`)
has no out-edges by typing. -/
inductive HasWalk {ι : Type} (out : ι → Finset (Option ι)) : Option ι → ℕ → Prop
  | nil (v : Option ι) : HasWalk out v 0
  | cons (j : ι) (v : Option ι) (k : ℕ) (hv : v ∈ out j) (h : HasWalk out v k) :
      HasWalk out (some j) (k + 1)

end RobustFcstAgg


