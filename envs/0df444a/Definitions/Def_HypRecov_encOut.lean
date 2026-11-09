-- Prove2me | Definitions.Def_HypRecov_encOut
-- name    : HypRecov_encOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:01.686422+00:00
-- url     : https://prove2.me/theorems/d60978bd-4893-48de-a323-30c9f9aa331c
-- title:
--   Output codes: an edge list and a weighted hypergraph
-- statement:
--   An output is written as a list of vertex sets (the recovered edges), each preceded by a $1$ and closed by a $0$, followed for Theorem 1.1 by the weighted hypergraph $\widehat H$ as a list of entries (vertex set, weight) in the same format. Each vertex set is a list of vertex numbers, so a family of $O(nk)$ edges of size $r$ takes $O(nrk\log n)$ bits, within the space budget.
--
--   The codes are injective, so a malformed output decodes to nothing and counts as an error.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §1.1, p.1 (PDF p.2); Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_HypRecov_encNat

namespace HypRecov

/-- **Output encodings.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection Streams*,
STOC 2027 submission (manuscript sha256 719dcfff…), §1.1, p.1 (PDF p.2): "Each edge is reported once
with all its vertices"; Theorem 1.1, p.2: the representation Ĥ.

`encEdges L`: a list of vertex sets, each preceded by `true`, closed by `false`. -/
def encEdges {n : ℕ} (L : List (Finset (Fin n))) : List Bool :=
  L.flatMap (fun e => true :: encSet e) ++ [false]

/-- The output of Theorem 1.1: the edge list `L`, then the weighted hypergraph `Ĥ` as a list of
(vertex set, weight) entries.

**Formalization Note.** The code is injective, so a malformed output decodes to nothing and is
incorrect. Vertex sets are written as vertex lists, not `n`-bit masks, so the `O(nrk)` recovered
memberships fit the space budget. -/
def encOut {n : ℕ} (L : List (Finset (Fin n))) (H : List (Finset (Fin n) × ℕ)) : List Bool :=
  encEdges L ++ (H.flatMap (fun p => true :: (encSet p.1 ++ encNat p.2)) ++ [false])

end HypRecov


