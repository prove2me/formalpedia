-- Prove2me | Definitions.Def_DDNNFNeg_BNode
-- name    : DDNNFNeg_BNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:09.167396+00:00
-- url     : https://prove2.me/theorems/2ce3c95e-6709-4c3a-b90c-eb70737083d6
-- title:
--   Vertex of a nondeterministic branching program
-- statement:
--   A **vertex** of a nondeterministic read-once branching program is one of:
--
--   1. a **sink** labelled $0$ or $1$;
--   2. a vertex labelled by a variable $x \in X$, with two outgoing edges labelled $0$ and $1$;
--   3. a vertex labelled $\vee$, with two unlabelled outgoing edges.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib

namespace DDNNFNeg

/-- A vertex of a nondeterministic read-once branching program whose vertices are indexed by
`Fin s` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9): a sink labelled `b ∈ {0,1}`, a vertex labelled by the
variable `v` with outgoing edges labelled `0` (to `lo`) and `1` (to `hi`), or a vertex
labelled `∨` with two unlabelled outgoing edges (to `l` and `r`). -/
inductive BNode (s : ℕ) (X : Type*) where
  /-- a sink labelled `b` -/
  | sink (b : Bool)
  /-- a vertex labelled by the variable `v`; the `0`-edge goes to `lo`, the `1`-edge to `hi` -/
  | test (v : X) (lo hi : Fin s)
  /-- a nondeterministic (`∨`) vertex with outgoing edges to `l` and `r` -/
  | choice (l r : Fin s)
  deriving DecidableEq

end DDNNFNeg


