-- Prove2me | Definitions.Def_RankRobustAssort_Reach
-- name    : RankRobustAssort_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:42.633097+00:00
-- url     : https://prove2.me/theorems/056f484a-5ddb-4156-bfdf-d99837485735
-- title:
--   Reachability $j\prec_{i_1\cdots i_M} i$ in $\mathcal G_{i_1\cdots i_M}$
-- statement:
--   Vertex $j$ is **reachable from vertex $i$**, written $j\prec_{i_1\cdots i_M} i$, if there is a directed path in $\mathcal G_{i_1\cdots i_M}$ from $i$ to $j$. By the paper's convention a directed path contains **at least one** directed edge, so a vertex is reachable from itself only through a cycle.
--
--   **Formalization Note.** The path is the transitive closure of the edge relation; the argument order of the Lean predicate mirrors the notation $j\prec i$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Definition EC.1, p.ec15

import Mathlib
import Definitions.Def_RankRobustAssort_edge

namespace RankRobustAssort

/-- Reachability in `𝒢_{i₁⋯i_M}`: `Reach P t j i` is the paper's `j ≺_{i₁⋯i_M} i`, "vertex `j` is
reachable from vertex `i`", meaning there is a directed path in `𝒢_{i₁⋯i_M}` **from `i` to `j`**,
and a directed path contains at least one directed edge.

Sturt, arXiv:2112.05010v4, Definition EC.1 and the convention following it, p.ec15.

Formalization Note: the path is `Relation.TransGen (edge P t) i j` (one or more edges, so a
vertex is not reachable from itself by the empty path). Note the argument order: `Reach P t j i`
mirrors the notation `j ≺ i`. -/
def Reach {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (j i : Fin (n + 1)) : Prop :=
  Relation.TransGen (edge P t) i j

end RankRobustAssort


