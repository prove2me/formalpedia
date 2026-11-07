-- Prove2me | Definitions.Def_LCPlanarSteiner_encArrIn
-- name    : LCPlanarSteiner_encArrIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:59.218922+00:00
-- url     : https://prove2.me/theorems/fc8baa3e-45d9-4478-810b-10fc42972db9
-- title:
--   Binary encoding of an arrival query
-- statement:
--   An arrival query consists of the graph $G$, the owned arcs $E_R$, the boundary vertices $B$, the purchased arcs $F$, the root $r$ and the cost budget $\Gamma$. It is encoded in binary with length-prefixed lists and $\Gamma$ as a binary rational.
--
--   **Formalization Note** Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.2, p.5; §3.1, p.5

import Mathlib
import Definitions.Def_LCPlanarSteiner_tokNet
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Binary encoding of an arrival query.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.2, p.5: "polynomial binary time … suffice to compute possibly infinite arrivals"; §3.1,
p.5: "The query graph has all pre-pruning owned edges E_R … For the current purchased union F, use
actual labels a(b) = dist_F(r, b)".

A query `(G, E_R, B, F, r, Γ)` is the graph, the owned arcs, the boundary vertices, the purchased
arcs, the root and the cost budget. `encArrIn` joins by the separator `3` the words of `G`
(`tokNet`), the three index lists (length first, binary), `r` in binary and `Γ` as a binary
rational.

**Formalization Note.** Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encArrIn (x : Net × List ℕ × List ℕ × List ℕ × ℕ × ℚ) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (tokNet x.1 ++ EulerSparsify.tokNatList x.2.1 ++ EulerSparsify.tokNatList x.2.2.1 ++
      EulerSparsify.tokNatList x.2.2.2.1 ++
      [OnlineCRS.Combine.encNat x.2.2.2.2.1, OnlineCRS.Combine.encRat x.2.2.2.2.2])

end LCPlanarSteiner


