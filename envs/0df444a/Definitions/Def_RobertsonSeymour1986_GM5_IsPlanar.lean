-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
-- name    : RobertsonSeymour1986_GM5_IsPlanar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:53:13.5033+00:00
-- url     : https://prove2.me/theorems/59f458b4-3ab0-4767-bc9a-0254033ca808
-- title:
--   Planar graph
-- statement:
--   A simple graph $H$ is **planar** if it has a plane drawing: vertices are distinct points of $\mathbb R^2$, edges are simple arcs between their ends, arcs avoid the other vertices, and distinct edges meet only at common endpoints.
--
--   Planarity of the excluded graph $H$ is the hypothesis of the main theorem (2.1) of Graph Minors V.
--
--   **Formalization Note** The definition repeats the platform's `FourColor.IsPlanar`. That definition was published in another Mathlib environment, so this mission cannot import it.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (1.5) p. 93, (2.1) p. 95 and Sect. 2 p. 94 (PDF pp. 2–4); mirrors platform definition FourColor_PlaneDrawing (id e7e035ad-264f-4baf-9cbf-7b80bd9c828c)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_PlaneDrawing

namespace RobertsonSeymour1986.GM5

/-- `H` is planar: it has a crossing-free drawing in the real plane by simple arcs.

Hypothesis of Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory
Ser. B 41 (1986), (1.5) p. 93 (PDF p. 2), (2.1) p. 95 (PDF p. 4) and Sect. 2, p. 94 (PDF p. 3).

**Formalization Note** Mirrors the published `FourColor.IsPlanar := Nonempty (FourColor.PlaneDrawing G)`
(definition `FourColor_PlaneDrawing`, id `e7e035ad-264f-4baf-9cbf-7b80bd9c828c`), which lives in
another Mathlib environment and cannot be imported here. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneDrawing G)

end RobertsonSeymour1986.GM5


