-- Prove2me | Definitions.Def_LCPlanarSteiner_windowGraph
-- name    : LCPlanarSteiner_windowGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:45.898124+00:00
-- url     : https://prove2.me/theorems/7b16ff3d-a275-404f-ad26-ce578823eaba
-- title:
--   The underlying graph of a window
-- statement:
--   The **underlying graph** of a window is the simple graph whose vertices are $\rho$ and the original vertices, in which two distinct vertices are adjacent when an arc of the window joins their images, or when they are $\rho$ and the head of the pendant arc.
--
--   The window is planar when this graph is planar.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.2, p.12

import Mathlib
import Definitions.Def_LCPlanarSteiner_Window

namespace LCPlanarSteiner

/-- **The simple underlying graph of a window `M`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.2, p.12: "There is a planar rooted graph M".

`windowGraph G W` is the simple graph on `Option (Fin n)` (`none` is the root `ρ`) in which two
distinct vertices are adjacent iff an arc of `A` joins their images, or they are `ρ` and the head
`v₀` of the pendant arc.

**Formalization Note.** Original vertices outside `Z ∪ V` are isolated; they do not affect
planarity. -/
def windowGraph (G : Net) (W : Window) : SimpleGraph (Option (Fin G.n)) :=
  SimpleGraph.fromRel fun x y =>
    (∃ e ∈ W.A, e < G.arcs.length ∧ (W.img (G.tl e)) = x.map Fin.val ∧
      (W.img (G.hd e)) = y.map Fin.val) ∨
    (∃ v₀, W.pend = some v₀ ∧ x = none ∧ y.map Fin.val = some v₀)

end LCPlanarSteiner


