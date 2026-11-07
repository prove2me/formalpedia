-- Prove2me | Definitions.Def_LCPlanarSteiner_rootPathSet
-- name    : LCPlanarSteiner_rootPathSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:21.249543+00:00
-- url     : https://prove2.me/theorems/6a072df8-bcbb-487e-b9cd-4b00d8c7616a
-- title:
--   Vertex set of a root path of a tree
-- statement:
--   For a tree $T$ with root $\rho$ and a vertex $x$, the **root path** of $x$ is the path of $T$ from $\rho$ to $x$, and $\mathrm{rootPathSet}(T, \rho, x)$ is its set of vertices. In a tree this path is unique.
--
--   Lemma 3.1 deletes the union of at most three such sets.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.1, p.5

import Mathlib

namespace LCPlanarSteiner

/-- **The vertex set of a root path of a tree.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.1, p.5: "at most three root paths of the tree can be found …".

For a tree `T` with root `ρ` and a vertex `x`, `rootPathSet T ρ x` is the set of vertices on the
path of `T` from `ρ` to `x`.

**Formalization Note.** A path is a `SimpleGraph.Walk` with `IsPath`; in a tree it is unique. -/
def rootPathSet {V : Type} (T : SimpleGraph V) (ρ x : V) : Set V :=
  {u | ∃ p : T.Walk ρ x, p.IsPath ∧ u ∈ p.support}

end LCPlanarSteiner


