-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_PlaneDrawing
-- name    : RobertsonSeymour1986_GM5_PlaneDrawing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:52:39.227815+00:00
-- url     : https://prove2.me/theorems/c5313f87-e6a8-4024-87ed-632a0a93b198
-- title:
--   Plane drawing of a simple graph
-- statement:
--   A **plane drawing** of a simple graph $G$ assigns
--
--   1. to each vertex $v$ a point $p(v)\in\mathbb R^2$, distinct vertices getting distinct points;
--   2. to each edge $vw$ a simple continuous arc from $p(v)$ to $p(w)$, the arc of $wv$ being the reverse of the arc of $vw$;
--
--   such that the arc of an edge passes through no vertex point other than its two ends, and two distinct edges meet only at common end points.
--
--   A graph is planar when such a drawing exists. This is the planarity notion of the paper's hypothesis "$H$ is a planar graph".
--
--   **Formalization Note** The structure repeats, field by field, the platform's published definition `FourColor.PlaneDrawing`. That definition was published in another Mathlib environment, so this mission cannot import it.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (1.5) p. 93 and (2.1) p. 95 (PDF pp. 2, 4), hypothesis "H is a planar graph" (standard notion, not defined in the paper); mirrors platform definition FourColor_PlaneDrawing (id e7e035ad-264f-4baf-9cbf-7b80bd9c828c)

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- A drawing of a simple graph in the real plane without crossings: vertices are distinct points,
each edge is a simple arc between its ends, the arc of an edge avoids every other vertex, and two
distinct edges meet only at common endpoints.

Planarity is the hypothesis on `H` in Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph,
J. Combin. Theory Ser. B 41 (1986), (1.5) p. 93 (PDF p. 2) and (2.1) p. 95 (PDF p. 4); the paper does
not define it and uses the standard notion.

**Formalization Note** This structure mirrors, field for field, the published platform definition
`FourColor.PlaneDrawing` (definition `FourColor_PlaneDrawing`, id
`e7e035ad-264f-4baf-9cbf-7b80bd9c828c`). That row lives in another Lean/Mathlib environment
(Mathlib `c5ea003`), so it cannot be imported here and is restated in this namespace. The only textual change is
`arc h.symm` for `arc (G.symm h)`, forced by the newer Mathlib (`SimpleGraph.symm` is now a
typeclass field); the meaning is the same. -/
structure PlaneDrawing {V : Type} (G : SimpleGraph V) where
  /-- The point representing each vertex. -/
  vertex : V → ℝ × ℝ
  vertex_injective : Function.Injective vertex
  /-- The arc representing the edge `vw`, from the point of `v` to the point of `w`. -/
  arc : ∀ {v w : V}, G.Adj v w → Path (vertex v) (vertex w)
  arc_injective : ∀ {v w : V} (h : G.Adj v w), Function.Injective (arc h)
  arc_reverse : ∀ {v w : V} (h : G.Adj v w), arc h.symm = (arc h).symm
  arc_avoids_vertices : ∀ {v w : V} (h : G.Adj v w) (t : unitInterval) (x : V),
    arc h t = vertex x → x = v ∨ x = w
  arcs_meet_only_at_endpoints :
    ∀ {v w x y : V} (h : G.Adj v w) (k : G.Adj x y) (s t : unitInterval),
      arc h s = arc k t →
        (v = x ∧ w = y) ∨ (v = y ∧ w = x) ∨
          ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))

end RobertsonSeymour1986.GM5


