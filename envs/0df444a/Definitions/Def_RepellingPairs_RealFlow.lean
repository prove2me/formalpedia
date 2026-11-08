-- Prove2me | Definitions.Def_RepellingPairs_RealFlow
-- name    : RepellingPairs_RealFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:14.719427+00:00
-- url     : https://prove2.me/theorems/51d163a3-e819-43e3-a6ff-7eb6d14cf14f
-- title:
--   Loads and costs of real flows $F$, $F'$
-- statement:
--   A real flow $F$ sends $F_{i,j}\ge0$ along the designated path $P_{i,j}$; a real flow $F'$ is a finitely supported nonnegative weight on terminal paths. The **load** of $F$ on an edge $e$ is
--
--   $$
--   \sum_{i,j}F_{i,j}\,\bigl|\{e\}\cap E(P_{i,j})\bigr|,
--   $$
--
--   and similarly for $F'$. The **cost** of $F$ is $\sum_{i,j}F_{i,j}D(i,j)$, and the cost of $F'$ is the total of weight times $D$ between the ends of each terminal path.
--
--   These are the quantities in the Farkas alternative of §3.
--
--   **Formalization Note** $F$ is indexed by ordered pairs, and its sum over ordered pairs is the paper's $\sum_{t,t'\in T}$. $P_{i,j}$ and $P_{j,i}$ use the same edges, so the order changes nothing.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3, pp.7–8

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath

set_option autoImplicit false

namespace RepellingPairs

universe u v

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k} [DecidableEq E]

/-- The amount of the real flow `F` through the edge `e` when `F i j` units are sent along the designated
path `P i j` (Property 1 and Property 2 of §3, pp.7–8). Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version
of October 23, 2026), §3, pp.7–8.

**Formalization Note.** `F` is indexed by ordered pairs, and the sum over ordered pairs is the paper's
`∑_{t,t′∈T}`. `P i j` and `P j i` use the same edges, so the order in a pair changes nothing. -/
noncomputable def realLoad (P : PathStructure G) (F : Fin k → Fin k → ℝ) (e : E) : ℝ :=
  ∑ i, ∑ j, F i j * (((P.path i j).1.edges.count e : ℕ) : ℝ)

/-- The amount of the real flow `F′`, a finitely supported weight on terminal paths, through `e`. -/
noncomputable def realPathLoad (F' : TerminalPath G →₀ ℝ) (e : E) : ℝ :=
  F'.sum fun q w => w * ((q.path.1.edges.count e : ℕ) : ℝ)

/-- The cost `∑_{t,t′} F_{t,t′} D(t,t′)` of the real flow `F` (Property 3, p.8). -/
noncomputable def realCost (D : Fin k → Fin k → ℝ) (F : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, F i j * D i j

/-- The cost `∑_{t,t′} F′_{t,t′} D(t,t′)` of the real flow `F′` (Property 3, p.8). -/
noncomputable def realPathCost (D : Fin k → Fin k → ℝ) (F' : TerminalPath G →₀ ℝ) : ℝ :=
  F'.sum fun q w => w * D q.src q.tgt

end RepellingPairs


