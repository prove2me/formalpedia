-- Prove2me | Definitions.Def_LCPlanarSteiner_tokNet
-- name    : LCPlanarSteiner_tokNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:38.429241+00:00
-- url     : https://prove2.me/theorems/0571d1b5-eba7-46a3-a597-2e49d33901f9
-- title:
--   Words of the binary encoding of a graph
-- statement:
--   The binary encoding of a graph lists the number $n$ of vertices, then the number of arcs, then each arc as four words: its tail and head in binary and its cost and length as binary rationals (numerator, a separator symbol, denominator).
--
--   These words, joined by a separator symbol, make the input length the usual bit size of the graph.
--
--   **Formalization Note** The alphabet is the published four-symbol `OnlineCRS.Combine.Sym` (two bits, a symbol inside rationals, a separator). Lists are length-prefixed with the published `ReserveLB.tokList`. All encodings of the mission are injective; this is proved in a verification file that is not uploaded.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2 (encoded in binary)

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

namespace LCPlanarSteiner

/-- **Words of the binary encoding of a graph.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "nonnegative rational edge
costs c_e and lengths ℓ_e, encoded in binary"; Theorem 1.2, p.2: "the complete binary input".

`tokNet G` is the word list: `n` in binary, then the arc list (its length first), each arc as four
words: tail and head in binary, cost and length as binary rationals.

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4` (`0`,
`1` bits, `2` inside a rational, `3` separator). Numbers are binary (published `encNat`, `encRat`),
lists are length-prefixed (published `ReserveLB.tokList`), and no word contains the separator `3`,
so the encodings built from these words are injective (proved in
`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def tokNet (G : Net) : List (List OnlineCRS.Combine.Sym) :=
  OnlineCRS.Combine.encNat G.n ::
    ReserveLB.tokList (fun a : ℕ × ℕ × ℚ × ℚ =>
      [OnlineCRS.Combine.encNat a.1, OnlineCRS.Combine.encNat a.2.1,
        OnlineCRS.Combine.encRat a.2.2.1, OnlineCRS.Combine.encRat a.2.2.2]) G.arcs

end LCPlanarSteiner


