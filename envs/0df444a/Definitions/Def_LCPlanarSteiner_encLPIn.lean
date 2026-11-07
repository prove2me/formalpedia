-- Prove2me | Definitions.Def_LCPlanarSteiner_encLPIn
-- name    : LCPlanarSteiner_encLPIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:35.132518+00:00
-- url     : https://prove2.me/theorems/bc76ff95-ef72-48d9-a971-9e4aec38e657
-- title:
--   Binary encoding of an LP point, padded by $\lceil 1/\varepsilon\rceil$ symbols
-- statement:
--   An LP point is encoded in binary (graph, pairs, root, $\varepsilon$, $h$, the lists $x$ and $y$, the flow records) followed by $\lceil 1/\varepsilon \rceil$ padding symbols, so that polynomial time in the input length is polynomial time jointly in the binary size and $1/\varepsilon$.
--
--   **Formalization Note** Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.6, p.15

import Mathlib
import Definitions.Def_LCPlanarSteiner_LPPoint
import Definitions.Def_LCPlanarSteiner_tokNet
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Binary encoding of an LP point, padded by `⌈1/ε⌉` symbols.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.6, p.15: "yields, in polynomial time … inverse accuracies are O(1/ε)".

`encLPIn P` joins by the separator `3`: the graph (`tokNet`), the pair list (length first, two
binary numbers each), the root, `ε` and `h`, the lists `x` and `y` (length first, binary rationals),
the flow records (length first; four binary numbers and a binary rational each), and one word of
`⌈1/ε⌉` zeros.

**Formalization Note.** The padding makes the time bound polynomial jointly in the binary size and
`1/ε`. Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encLPIn (P : LPPoint) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (tokNet P.net ++
      ReserveLB.tokList (fun d : ℕ × ℕ =>
        [OnlineCRS.Combine.encNat d.1, OnlineCRS.Combine.encNat d.2]) P.dem ++
      [OnlineCRS.Combine.encNat P.root, OnlineCRS.Combine.encRat P.ε, OnlineCRS.Combine.encRat P.h] ++
      ReserveLB.tokList (fun q : ℚ => [OnlineCRS.Combine.encRat q]) P.x ++
      ReserveLB.tokList (fun q : ℚ => [OnlineCRS.Combine.encRat q]) P.y ++
      ReserveLB.tokList (fun rc : ℕ × ℕ × ℕ × ℕ × ℚ =>
        [OnlineCRS.Combine.encNat rc.1, OnlineCRS.Combine.encNat rc.2.1,
          OnlineCRS.Combine.encNat rc.2.2.1, OnlineCRS.Combine.encNat rc.2.2.2.1,
          OnlineCRS.Combine.encRat rc.2.2.2.2]) P.flows ++
      [List.replicate ⌈1 / P.ε⌉₊ (0 : OnlineCRS.Combine.Sym)])

end LCPlanarSteiner


