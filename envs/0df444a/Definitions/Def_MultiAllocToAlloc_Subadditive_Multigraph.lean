-- Prove2me | Definitions.Def_MultiAllocToAlloc_Subadditive_Multigraph
-- name    : MultiAllocToAlloc_Subadditive_Multigraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:09:13.778623+00:00
-- url     : https://prove2.me/theorems/ba9f5e5a-b83e-4bc7-8b98-d6e50d7d4b90
-- title:
--   Multigraph allocation instances and orientations (§2.2)
-- statement:
--   A `Multigraph n m` has vertex set `Fin n` (the agents) and edge set `Fin m` (the items); every edge $e$ has two distinct endpoints `(ends e).1 ≠ (ends e).2`, and parallel edges are allowed. $M_i$ (`G.incident i`) is the set of edges incident with vertex $i$. A valuation profile $v$ makes $G$ a **multigraph allocation instance** (`IsMultigraphInstance G v`) when each agent's value depends only on the items incident with her, $v_i(T)=v_i(T\cap M_i)$ for every bundle $T$, i.e. every other item has $0$ marginal value (p. 9). An allocation is an **orientation** $o$ (`G.IsOrientation o`): every edge $e$ goes to one of its endpoints $o(e)$, and agent $i$ receives `bundleOf o i` $=\{e : o(e)=i\}$.
-- source:
--   Feige, arXiv:2506.21493v1, §2.2, p. 9

import Mathlib

namespace MultiAllocToAlloc.Subadditive

/-- A loopless multigraph on the vertex set `Fin n` with edge set `Fin m`
(Feige, arXiv:2506.21493v1, §2.2, p. 9): every edge `e` has two distinct endpoints
`(ends e).1 ≠ (ends e).2`; parallel edges are allowed. -/
structure Multigraph (n m : ℕ) where
  /-- The two endpoints of each edge. -/
  ends : Fin m → Fin n × Fin n
  /-- No edge is a loop. -/
  loopless : ∀ e : Fin m, (ends e).1 ≠ (ends e).2

namespace Multigraph

variable {n m : ℕ}

/-- `M_i`: the set of edges incident with vertex `i`. -/
def incident (G : Multigraph n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun e => (G.ends e).1 = i ∨ (G.ends e).2 = i)

/-- An orientation of `G`: every edge `e` is assigned to (oriented towards) one of its two
endpoints `o e`. -/
def IsOrientation (G : Multigraph n m) (o : Fin m → Fin n) : Prop :=
  ∀ e : Fin m, o e = (G.ends e).1 ∨ o e = (G.ends e).2

end Multigraph

/-- The bundle that agent `i` receives under the assignment `o` of items to agents:
the items `e` with `o e = i`. -/
def bundleOf {n m : ℕ} (o : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun e => o e = i)

/-- A multigraph allocation instance (Feige, arXiv:2506.21493v1, §2.2, p. 9): agents are the
vertices of `G`, items are its edges, and agent `i`'s valuation depends only on the items
incident with `i` (every other item has `0` marginal value):
`v i T = v i (T ∩ M_i)` for every bundle `T`. Allocations in such instances are orientations,
agent `i` receiving `bundleOf o i`. -/
def IsMultigraphInstance {n m : ℕ} (G : Multigraph n m) (v : Fin n → Finset (Fin m) → ℝ) :
    Prop :=
  ∀ (i : Fin n) (T : Finset (Fin m)), v i T = v i (T ∩ G.incident i)

end MultiAllocToAlloc.Subadditive


