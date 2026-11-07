-- Prove2me | Definitions.Def_LCPlanarSteiner_encSepIn
-- name    : LCPlanarSteiner_encSepIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:35.099917+00:00
-- url     : https://prove2.me/theorems/f9c76411-cb1c-44f5-ba22-97086f866759
-- title:
--   Binary encoding of a separator input
-- statement:
--   A separator input is the number $n$ of vertices, the edge list of the graph, the edge list of the spanning tree, the root and the list of $n$ vertex weights. It is encoded in binary with length-prefixed lists.
--
--   **Formalization Note** No embedding of the graph is part of the input. The encoding is injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.1, p.5

import Mathlib
import Definitions.Def_EulerSparsify_joinW
import Definitions.Def_OnlineCRS_Combine_encRat

namespace LCPlanarSteiner

/-- **Binary encoding of a separator input (graph, spanning tree, root, weights).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.1, p.5: "Given a plane graph, a rooted spanning tree, and nonnegative vertex weights,
… in polynomial time".

An input `(n, E, T, ρ, w)` is the number of vertices, the edge list of the graph, the edge list of
the tree, the root and the list of vertex weights. `encSepIn` joins by the separator `3`: `n`, the
two edge lists (length first, each edge as two binary numbers), `ρ`, and the weight list (length
first, binary rationals).

**Formalization Note.** Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). No
embedding is part of the input. -/
def encSepIn (x : ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × List ℚ) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (OnlineCRS.Combine.encNat x.1 ::
      (ReserveLB.tokList (fun e : ℕ × ℕ =>
          [OnlineCRS.Combine.encNat e.1, OnlineCRS.Combine.encNat e.2]) x.2.1 ++
        ReserveLB.tokList (fun e : ℕ × ℕ =>
          [OnlineCRS.Combine.encNat e.1, OnlineCRS.Combine.encNat e.2]) x.2.2.1 ++
        [OnlineCRS.Combine.encNat x.2.2.2.1] ++
        ReserveLB.tokList (fun q : ℚ => [OnlineCRS.Combine.encRat q]) x.2.2.2.2))

end LCPlanarSteiner


