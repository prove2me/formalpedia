-- Prove2me | Definitions.Def_LCPlanarSteiner_IsSPath
-- name    : LCPlanarSteiner_IsSPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:30.490218+00:00
-- url     : https://prove2.me/theorems/c8d63870-560f-4d5f-a882-0a7debb13dc1
-- title:
--   Simple directed paths
-- statement:
--   A **simple directed path** from $s$ to $t$ is a directed walk from $s$ to $t$ whose vertex sequence has no repeated vertex. The empty list is the only simple path from $s$ to $s$.
--
--   Every path returned by the algorithms of the paper is simple, because cycle erasure of a walk with nonnegative lengths gives a simple path that is no longer.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4, p.9 (cycle erasure gives an original pair path); proof of Lemma 4.6, p.15

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsWalk

namespace LCPlanarSteiner

/-- **A simple directed path.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4, p.9: "cycle erasure of their
concatenation gives an original pair path"; proof of Lemma 4.6, p.15: "Cycle erasure gives an
original simple pair path."

`IsSPath G s t p`: `p` is a directed walk from `s` to `t` that visits no vertex twice. The empty
list is the only simple path from `s` to `s`.

**Formalization Note.** Vertex-distinctness is `List.Nodup` of the vertex sequence `verts G s p`. -/
def IsSPath (G : Net) (s t : ℕ) (p : List ℕ) : Prop :=
  IsWalk G s t p ∧ (verts G s p).Nodup

end LCPlanarSteiner


