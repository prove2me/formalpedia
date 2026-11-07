-- Prove2me | Definitions.Def_LCPlanarSteiner_tokRootData
-- name    : LCPlanarSteiner_tokRootData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:31.886639+00:00
-- url     : https://prove2.me/theorems/77517308-616d-40fa-a5e9-6b96580ffd93
-- title:
--   Words of the binary encoding of a rooted datum
-- statement:
--   The binary encoding of a rooted datum lists the graph, the root, the terminals (each with its bound and its distribution of length-prefixed paths and rational weights) and the purchases.
--
--   **Formalization Note** Words over the published alphabet; the encodings built from them are injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.8, pp.8–9

import Mathlib
import Definitions.Def_LCPlanarSteiner_RootData
import Definitions.Def_LCPlanarSteiner_tokNet
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Words of the binary encoding of a rooted datum.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.8, pp.8–9: "Its time is polynomial in the binary supplied description".

`tokRootData R`: the graph (`tokNet`), the root in binary, the terminal list (length first; per
terminal: the terminal in binary, `b_t` as a binary rational, and its distribution, length first,
each entry a length-prefixed arc list and a binary rational weight), and the purchase list (length
first, binary rationals).

**Formalization Note.** Words over the published alphabet; the encodings built from them are
injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def tokRootData (R : RootData) : List (List OnlineCRS.Combine.Sym) :=
  tokNet R.net ++ [OnlineCRS.Combine.encNat R.root] ++
    ReserveLB.tokList (fun τ : ℕ × ℚ × List (List ℕ × ℚ) =>
      [OnlineCRS.Combine.encNat τ.1, OnlineCRS.Combine.encRat τ.2.1] ++
        ReserveLB.tokList (fun pw : List ℕ × ℚ =>
          EulerSparsify.tokNatList pw.1 ++ [OnlineCRS.Combine.encRat pw.2]) τ.2.2) R.terms ++
    ReserveLB.tokList (fun q : ℚ => [OnlineCRS.Combine.encRat q]) R.x

end LCPlanarSteiner


