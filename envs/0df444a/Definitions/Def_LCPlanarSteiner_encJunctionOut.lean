-- Prove2me | Definitions.Def_LCPlanarSteiner_encJunctionOut
-- name    : LCPlanarSteiner_encJunctionOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:37.991204+00:00
-- url     : https://prove2.me/theorems/5e7a1f26-9d45-4560-9356-7d7ae97d4fdd
-- title:
--   Binary encoding of a junction with its pair paths
-- statement:
--   The output of the junction search is the arc list of $H'$, the list of pair indices $I$ and one path per listed pair, all encoded as length-prefixed lists of binary numbers.
--
--   **Formalization Note** Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.6, p.15

import Mathlib
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Binary encoding of a junction with its pair paths.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.6, p.15: "a nonempty original junction … with complete original pair lengths at most
(1 + ε)h".

An output `(H′, I, paths)` is the arc list of `H′`, the list of pair indices `I`, and one arc-index
path per listed pair. `encJunctionOut` joins by the separator `3` the two length-prefixed index lists
and the length-prefixed list of length-prefixed paths.

**Formalization Note.** Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encJunctionOut (o : List ℕ × List ℕ × List (List ℕ)) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (EulerSparsify.tokNatList o.1 ++ EulerSparsify.tokNatList o.2.1 ++
      ReserveLB.tokList EulerSparsify.tokNatList o.2.2)

end LCPlanarSteiner


