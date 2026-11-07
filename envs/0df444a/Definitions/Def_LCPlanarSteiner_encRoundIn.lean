-- Prove2me | Definitions.Def_LCPlanarSteiner_encRoundIn
-- name    : LCPlanarSteiner_encRoundIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:08:01.631193+00:00
-- url     : https://prove2.me/theorems/9679170b-4f5d-43b6-8fad-22db76430860
-- title:
--   Binary encoding of a rounding input, padded by $\lceil H/\delta\rceil$ symbols
-- statement:
--   The input of the rounding algorithm of Lemma 3.8 is the binary encoding of the rooted datum, of $H$ and of $\delta$, followed by $\lceil H/\delta \rceil$ padding symbols.
--
--   The padding makes "time polynomial in the input length" equal to "time polynomial in the binary description and $1 + H/\delta$".
--
--   **Formalization Note** Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.8, pp.8–9

import Mathlib
import Definitions.Def_LCPlanarSteiner_tokRootData

namespace LCPlanarSteiner

/-- **Binary encoding of a rounding input `(R, H, δ)`, padded by `⌈H/δ⌉` symbols.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.8, pp.8–9: "Its time is polynomial in the binary supplied description and 1 + H/δ."

`encRoundIn (R, H, δ)` joins by the separator `3` the words of `R`, `H` and `δ` as binary rationals,
and one word of `⌈H/δ⌉` zeros.

**Formalization Note.** The padding makes "polynomial in the input length" equal to "polynomial in
the binary description and `1 + H/δ`". Injective (`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encRoundIn (x : RootData × ℚ × ℚ) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (tokRootData x.1 ++ [OnlineCRS.Combine.encRat x.2.1, OnlineCRS.Combine.encRat x.2.2] ++
      [List.replicate ⌈x.2.1 / x.2.2⌉₊ (0 : OnlineCRS.Combine.Sym)])

end LCPlanarSteiner


