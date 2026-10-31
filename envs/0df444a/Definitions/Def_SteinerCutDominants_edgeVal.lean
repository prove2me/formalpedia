-- Prove2me | Definitions.Def_SteinerCutDominants_edgeVal
-- name    : SteinerCutDominants_edgeVal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:17.666222+00:00
-- url     : https://prove2.me/theorems/e03ed652-5b4c-4794-a532-9d13b3b9f9f4
-- title:
--   Edge vectors as functions of node pairs
-- statement:
--   For a vector $f$ indexed by the edges of $G$ and nodes $x,y$, the value $f(xy)$ if $xy$ is an edge and $0$ otherwise. This is a device of the formalization, with no counterpart in the paper: it lets relations between graphs on different vertex types compare weights through maps on vertices.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, (auxiliary; no counterpart in the paper)

import Mathlib

namespace SteinerCutDominants

/-- The value on the pair `x, y` of a vector indexed by the edges of `G`, extended by `0` to pairs
that are not edges. An auxiliary device of the formalization (no paper counterpart): it lets the
gluing, subdivision and isomorphism relations compare edge vectors of graphs on different vertex
types through maps on vertices. -/
def edgeVal {V α : Type} [Zero α] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : G.edgeSet → α) (x y : V) : α :=
  if h : G.Adj x y then f ⟨s(x, y), (SimpleGraph.mem_edgeSet G).2 h⟩ else 0

end SteinerCutDominants


