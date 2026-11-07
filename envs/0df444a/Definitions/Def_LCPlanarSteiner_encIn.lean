-- Prove2me | Definitions.Def_LCPlanarSteiner_encIn
-- name    : LCPlanarSteiner_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:34.131145+00:00
-- url     : https://prove2.me/theorems/9dae9f91-6c08-4d7e-94d2-cac108f486ee
-- title:
--   Binary encoding of a forest instance, padded by $\lceil 1/\varepsilon\rceil$ symbols
-- statement:
--   The input of the forest algorithm is the binary encoding of the instance (the graph, $h$, $\varepsilon$ and the demand list), followed by one word of $\lceil 1/\varepsilon \rceil$ padding symbols.
--
--   The padding makes "time polynomial in the input length" equal to "time polynomial jointly in the binary size and $1/\varepsilon$", as required by Theorem 1.2.
--
--   **Formalization Note** Words are joined by the separator symbol; the encoding is injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Theorem 1.2, p.2 (running time polynomial jointly in the complete binary input and $1/\varepsilon$)

import Mathlib
import Definitions.Def_LCPlanarSteiner_Inst
import Definitions.Def_LCPlanarSteiner_tokNet
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Binary encoding of a forest instance, padded by `⌈1/ε⌉` symbols.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Theorem 1.2, p.2: "Its running time is
polynomial jointly in the complete binary input and 1/ε."

`encIn I` joins by the separator `3` the words: the graph (`tokNet`), `h` and `ε` as binary
rationals, the demand list (length first, each pair as two binary numbers), and finally one word of
`⌈1/ε⌉` zeros.

**Formalization Note.** The padding word makes "time polynomial in the input length" the same as
"time polynomial jointly in the binary size and `1/ε`": its length is `⌈1/ε⌉ ≥ 1/ε`, and conversely
`⌈1/ε⌉ ≤ 1/ε + 1`. The encoding is injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encIn (I : Inst) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (tokNet I.net ++ [OnlineCRS.Combine.encRat I.h, OnlineCRS.Combine.encRat I.ε] ++
      ReserveLB.tokList (fun d : ℕ × ℕ =>
        [OnlineCRS.Combine.encNat d.1, OnlineCRS.Combine.encNat d.2]) I.dem ++
      [List.replicate ⌈1 / I.ε⌉₊ (0 : OnlineCRS.Combine.Sym)])

end LCPlanarSteiner


