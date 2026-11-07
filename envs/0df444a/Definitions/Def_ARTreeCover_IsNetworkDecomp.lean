-- Prove2me | Definitions.Def_ARTreeCover_IsNetworkDecomp
-- name    : ARTreeCover_IsNetworkDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:26.342865+00:00
-- url     : https://prove2.me/theorems/8319eed8-23b1-47cf-878d-94f3426fa5a2
-- title:
--   $(Z,\Gamma)$-network decomposition of an unweighted graph
-- statement:
--   A strong **$(Z,\Gamma)$-network decomposition** of an unweighted graph $L=(V,E)$ is a coloring $f:V\to\{1,\dots,Z\}$ such that for every color $c$, every connected component of the induced graph $L[f^{-1}(c)]$ has strong radius at most $\Gamma$: some vertex of the component reaches each vertex of the component within $\Gamma$ edges inside $L[f^{-1}(c)]$.
--
--   **Formalization Note** The statement quantifies over a vertex $x$ of color $c$ and asks for $z$ of color $c$ with hop distance at most $\Gamma$ to every vertex reachable from $x$ in $L[f^{-1}(c)]$. Since $x$ reaches itself, $z$ lies in the component of $x$.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 13, pp.21–22 (PDF pp.24–25)

import Mathlib

namespace ARTreeCover

/-- `IsNetworkDecomp L Z Γ f`: the coloring `f : V → {1, …, Z}` (here `Fin Z`) is a (strong)
`(Z, Γ)`-network decomposition of the unweighted graph `L`.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 13, pp.21–22 (PDF pp.24–25): "a
function f : V → {1, 2, ..., Z} such that for every color 1 ≤ c ≤ Z, every connected component in
the graph L[f⁻¹(c)] has (strong) radius at most Γ."

**Formalization Note.** `L` is unweighted, so the radius is in hops: for each color `c` and each
vertex `x` of color `c`, some vertex `z` of color `c` reaches, inside `L[f⁻¹(c)]`, every vertex of
`x`'s component within `Γ` edges (`SimpleGraph.edist` of the induced graph). Such a `z` lies in
that component, so it is a center of the component in `L[f⁻¹(c)]`. -/
def IsNetworkDecomp {V : Type} (L : SimpleGraph V) (Z Γ : ℕ) (f : V → Fin Z) : Prop :=
  ∀ c : Fin Z, ∀ x : ↥({v | f v = c} : Set V), ∃ z : ↥({v | f v = c} : Set V),
    ∀ y : ↥({v | f v = c} : Set V), (L.induce {v | f v = c}).Reachable x y →
      (L.induce {v | f v = c}).edist z y ≤ Γ

end ARTreeCover


