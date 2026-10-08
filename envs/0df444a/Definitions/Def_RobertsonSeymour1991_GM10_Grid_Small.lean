-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Grid_Small
-- name    : RobertsonSeymour1991_GM10_Grid_Small
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:24.534394+00:00
-- url     : https://prove2.me/theorems/51dc1cb5-d50f-4933-ad4f-f244614a68ac
-- title:
--   §7, p. 172 — small edge set in a grid
-- statement:
--   An edge set $X$ of the $\theta$-grid is **small** if its edge boundary has fewer than $\theta$ vertices and no complete row edge set lies inside $X$:
--
--   $$X\text{ is small}\quad\Longleftrightarrow\quad |\partial(X)|<\theta\ \text{and}\ \forall i\in\{1,\ldots,\theta\},\ E(P_i)\nsubseteq X.$$
--
--   This is the small-side condition used to select the orientations forming the grid tangle.
--
--   **Formalization Note** The grid's rows have $0$-based `Fin` indices. Both clauses are retained: forgetting the row exclusion would change the assertion of (7.2) and invalidate the proposed tangle. The boundary uses existence of an incident edge on each side.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 172, §7, paragraph before (7.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Grid_GridHypergraph

namespace RobertsonSeymour1991.GM10.Grid

/-- §7, p. 172: `X` is small when fewer than `θ` vertices lie in its edge boundary and no
full horizontal row has all its edges in `X`. -/
def IsSmall (θ : ℕ) (X : Set (RobertsonSeymour1986.GM5.grid θ).edgeSet) : Prop :=
  (boundary θ X).ncard < θ ∧ ∀ i : Fin θ, ¬ rowEdges θ i ⊆ X

end RobertsonSeymour1991.GM10.Grid


