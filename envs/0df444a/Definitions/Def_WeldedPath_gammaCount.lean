-- Prove2me | Definitions.Def_WeldedPath_gammaCount
-- name    : WeldedPath_gammaCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:27.439513+00:00
-- url     : https://prove2.me/theorems/2ac3af16-3cfb-458d-968b-5d74650f9e23
-- title:
--   The edge-color count $\gamma(\alpha',c)$ of a column
-- statement:
--   For a color $\alpha'$ and a column $c$, $\gamma(\alpha',c)$ is the number of tree edges of color $\alpha'$ whose child lies in column $c$, counted in $T_1$ or in $T_2$ separately. The edges in column $c$ are those between columns $c-1$ and $c$; in $T_1$ their child lies in column $c$, in $T_2$ in column $c-1$.
--
--   These counts show that each color class of a column has about a third of its edges.
--
--   **Formalization Note** $T_1$ consists of the indices below $2^{n+1}-1$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Lemma 3.2, p.15

import Mathlib
import Definitions.Def_WeldedPath_WeldedInstance

namespace WeldedPath

open WeldedInstance

/-- The number `γ(α′, c)` (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder,
arXiv:2611.05912 (sha256 b31400a0…), Lemma 3.2, p.15) of tree edges of color `α′` whose child
lies in column `c` and in the tree `T_1` (`side = true`) or `T_2` (`side = false`).

**Formalization Note.** `T_1` is the set of indices below `2^{n+1} − 1` (the exit index), `T_2` the
rest; a tree edge is named by its child, which has a parent. -/
def gammaCount {n : ℕ} (G : WeldedInstance n) (side : Bool) (α' : Fin 3) (c : ℕ) : ℕ :=
  ((Finset.range (numV n)).filter fun v =>
    (parent n v).isSome ∧ (v < exitIdx n ↔ side = true) ∧ col n v = c ∧
      G.color (.tree v) = α').card

end WeldedPath


