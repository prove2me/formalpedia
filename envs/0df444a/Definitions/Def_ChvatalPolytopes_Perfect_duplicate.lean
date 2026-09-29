-- Prove2me | Definitions.Def_ChvatalPolytopes_Perfect_duplicate
-- name    : ChvatalPolytopes_Perfect_duplicate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:12:47.249881+00:00
-- url     : https://prove2.me/theorems/7d20f9a8-b596-4e93-987f-32fafeb6c271
-- title:
--   Duplication of a vertex (§3)
-- statement:
--   Let $G=(V,E)$ be a graph and $u\in V$. To **duplicate** the vertex $u$ means to add a new vertex $u'$ and join it by edges to all the neighbours of $u$, but not to $u$ itself. The resulting graph $G\circ u$ has vertex set $V\cup\{u'\}$; two old vertices $v,w$ are adjacent in it exactly when they are adjacent in $G$, and $u'$ is adjacent to an old vertex $w$ exactly when $uw\in E$.
--
--   Duplication is the operation in Lovász's second theorem: perfection is preserved under it, and iterating it gives the multiplication of a vertex by a positive integer used in the proof of Theorem 3.1.
--
--   **Formalization Note** The new graph lives on `Option V`: `some v` is the old vertex $v$ and `none` is the new vertex $u'$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 140, §3 (definition of duplication)

import Mathlib

namespace ChvatalPolytopes.Perfect

/-- **Duplication of a vertex** (Chvátal 1975, p. 140): the graph obtained from `G` by adding a
new vertex `u'` and joining it by edges to all the neighbours of `u`, but not to `u` itself.
The vertex set is `Option V`: `some v` is the old vertex `v` and `none` is the new vertex `u'`.
Old vertices keep their adjacencies; `u'` is adjacent to `some w` exactly when `G.Adj u w`. -/
def duplicate {V : Type*} (G : SimpleGraph V) (u : V) : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some v, some w => G.Adj v w
    | none, some w => G.Adj u w
    | some v, none => G.Adj v u
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

end ChvatalPolytopes.Perfect


