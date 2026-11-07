-- Prove2me | Definitions.Def_LCPlanarSteiner_sgOf
-- name    : LCPlanarSteiner_sgOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:26.408949+00:00
-- url     : https://prove2.me/theorems/a76952db-f420-4b12-8e5d-916561e2cb61
-- title:
--   The simple graph of an edge list
-- statement:
--   For $n$ and a list $E$ of pairs, the simple graph on $\{0, \dots, n-1\}$ has $u \ne v$ adjacent when $(u, v)$ or $(v, u)$ occurs in $E$. Pairs with an endpoint outside the vertex set and loops are ignored.
--
--   Graphs and spanning trees given to the separator algorithm of Lemma 3.1 are edge lists of this kind.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.1, p.5

import Mathlib

namespace LCPlanarSteiner

/-- **The simple graph given by an edge list.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.1, p.5: "Given a plane graph, a rooted spanning tree, and nonnegative vertex
weights".

`sgOf n E` is the simple graph on the vertices `0, …, n − 1` in which `u ≠ v` are adjacent iff
`(u, v)` or `(v, u)` occurs in the list `E`.

**Formalization Note.** Entries with an endpoint `≥ n` and loops `(u, u)` are ignored. Graphs given
to the separator algorithm of Lemma 3.1 are edge lists of this kind (no embedding is supplied). -/
def sgOf (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (u.val, v.val) ∈ E

end LCPlanarSteiner


