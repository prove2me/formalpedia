-- Prove2me | Definitions.Def_LCPlanarSteiner_IsWalk
-- name    : LCPlanarSteiner_IsWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:24.151016+00:00
-- url     : https://prove2.me/theorems/a2a674f5-5012-4d80-974e-f1d37ccf64e9
-- title:
--   Directed walks given by their arcs
-- statement:
--   A list $p = (e_1, \dots, e_k)$ of arc indices is a **directed walk** from $s$ to $t$ in $G$ when every index is an arc of $G$, $\mathrm{tail}(e_1) = s$, $\mathrm{tail}(e_{j+1}) = \mathrm{head}(e_j)$ for $j < k$, and $\mathrm{head}(e_k) = t$; the empty list is the walk from $s$ to $s$.
--
--   Its **vertex sequence** is $(s, \mathrm{head}(e_1), \dots, \mathrm{head}(e_k))$, and $\mathrm{vtx}(s, p, j)$ denotes its $j$-th entry ($j = 0$ gives $s$). Prefixes and suffixes of a walk are its initial and final segments of arcs.
--
--   Walks are the basic objects from which paths, distances and arrivals are built.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2 (original paths); §3, p.4 (cycle erasure)

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **A directed walk given by its arcs.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2 ("an original path of length
at most h") and §3, p.4 ("Nonnegative lengths permit cycle erasure").

`IsWalk G s t p` says that the list of arc indices `p` is a directed walk from `s` to `t` in `G`:
every index is in range, the first arc leaves `s`, each arc leaves the head of the previous one, and
the last arc enters `t`. The empty list is the walk from `s` to `s`.

`verts G s p` is the vertex sequence `s, head(p₁), head(p₂), …` of the walk, and `vtx G s p k` its
`k`-th vertex (position `0` is `s`).

**Formalization Note.** Walks may repeat vertices; simple paths are `IsSPath`. Distances are
always realised by walks (`DistLE`); with nonnegative lengths this is the same as by simple paths. -/
def IsWalk (G : Net) : ℕ → ℕ → List ℕ → Prop
  | s, t, [] => s = t
  | s, t, e :: p => e < G.arcs.length ∧ G.tl e = s ∧ IsWalk G (G.hd e) t p

/-- The vertex sequence of a walk starting at `s`. -/
def verts (G : Net) (s : ℕ) (p : List ℕ) : List ℕ := s :: p.map G.hd

/-- The `k`-th vertex of the walk `p` started at `s` (`vtx G s p 0 = s`). -/
def vtx (G : Net) (s : ℕ) (p : List ℕ) (k : ℕ) : ℕ := (verts G s p).getD k s

end LCPlanarSteiner


