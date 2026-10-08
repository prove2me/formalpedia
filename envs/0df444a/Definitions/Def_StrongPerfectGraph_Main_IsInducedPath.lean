-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsInducedPath
-- name    : StrongPerfectGraph_Main_IsInducedPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:05:10.954677+00:00
-- url     : https://prove2.me/theorems/33511762-1633-49e0-bd8a-b50bc96a6468
-- title:
--   Induced path
-- statement:
--   Let $G$ be a finite simple graph. A path is a nonempty induced subgraph that is connected, is not a cycle, and has degree at most two at every vertex. Represent its vertices by a list $p=(v_0,\ldots,v_\ell)$ in path order. The list has no repeated vertex, and its edges are exactly the pairs in consecutive positions:
--
--   $$v_i v_j\in E(G)\quad\Longleftrightarrow\quad |i-j|=1.$$
--
--   The path has length $\ell$, and a one-vertex path has length zero. Reversing the list represents the same path. Applied to $\overline G$, the definition gives an antipath. This definition preserves inducedness when the paper reasons about path parity.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 53, §1, definition of a path

import Mathlib

namespace StrongPerfectGraph.Main

/-- A nonempty induced path, presented in one of its two orientations. -/
def IsInducedPath {V : Type*} (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧
    ∀ i j : Fin p.length,
      G.Adj (p.get i) (p.get j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)

end StrongPerfectGraph.Main


