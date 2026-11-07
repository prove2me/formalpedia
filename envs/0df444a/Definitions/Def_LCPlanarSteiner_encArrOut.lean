-- Prove2me | Definitions.Def_LCPlanarSteiner_encArrOut
-- name    : LCPlanarSteiner_encArrOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:30.428281+00:00
-- url     : https://prove2.me/theorems/d963d97d-037f-4282-ad6e-bb40c6cac8e1
-- title:
--   Binary encoding of arrivals and their extensions
-- statement:
--   The answer to an arrival query is one entry per vertex $v$: a flag saying whether $A(v)$ is finite, the value $A(v)$ as a rational, and the extension $Q_v$ as a list of arc indices. The list is encoded with its length and each entry as a bit, a binary rational and a length-prefixed list.
--
--   **Formalization Note** A cleared flag means $A(v) = +\infty$; the value and the list are then ignored. Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.2, p.5

import Mathlib
import Definitions.Def_EulerSparsify_joinW
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encRat

namespace LCPlanarSteiner

/-- **Binary encoding of arrivals with their extensions.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.2, p.5: "compute possibly infinite arrivals A(v) and original owned extensions Q_v
for finite values".

An answer is a list with one entry `(finite, A(v), Q_v)` per vertex `v`: a flag (`false` means
`A(v) = +∞`), the arrival as a rational, and the extension as a list of arc indices. `encArrOut`
joins by the separator `3` the length of the list and, per entry, the flag bit, the binary rational
and the length-prefixed arc list.

**Formalization Note.** Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encArrOut (o : List (Bool × ℚ × List ℕ)) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (ReserveLB.tokList (fun a : Bool × ℚ × List ℕ =>
      [[OnlineCRS.Combine.bit a.1], OnlineCRS.Combine.encRat a.2.1] ++
        EulerSparsify.tokNatList a.2.2) o)

end LCPlanarSteiner


