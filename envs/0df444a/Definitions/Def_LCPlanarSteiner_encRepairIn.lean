-- Prove2me | Definitions.Def_LCPlanarSteiner_encRepairIn
-- name    : LCPlanarSteiner_encRepairIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:08:17.27145+00:00
-- url     : https://prove2.me/theorems/4f153bd2-a99b-4819-b5e2-eb3d233b4026
-- title:
--   Binary encoding of an additive-repair input, padded by $\lceil 1/\sigma\rceil$ symbols
-- statement:
--   The input of the additive repair (7) is the binary encoding of the rooted datum, of $B$ and of $E$, followed by $\lceil 1/\sigma \rceil$ padding symbols, where $\sigma = \min\{1, 2E/B\}$.
--
--   The padding makes "time polynomial in the input length" equal to "time polynomial in the binary description and the inverse accuracy".
--
--   **Formalization Note** Injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.4, display (7), p.9

import Mathlib
import Definitions.Def_LCPlanarSteiner_tokRootData

namespace LCPlanarSteiner

/-- **Binary encoding of an additive-repair input `(R, B, E)`, padded by `⌈1/σ⌉` symbols.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.4, display (7), p.9: "put σ = min{1, 2E/B} … Both choices have the claimed polynomial time
in the binary supplied description and inverse accuracy."

`encRepairIn (R, B, E)` joins by the separator `3` the words of `R`, `B` and `E` as binary rationals,
and one word of `⌈1/σ⌉` zeros, `σ = min{1, 2E/B}`.

**Formalization Note.** The padding makes "polynomial in the input length" equal to "polynomial in
the binary description and the inverse accuracy `1/σ`". Injective
(`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encRepairIn (x : RootData × ℚ × ℚ) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW
    (tokRootData x.1 ++ [OnlineCRS.Combine.encRat x.2.1, OnlineCRS.Combine.encRat x.2.2] ++
      [List.replicate ⌈1 / min 1 (2 * x.2.2 / x.2.1)⌉₊ (0 : OnlineCRS.Combine.Sym)])

end LCPlanarSteiner


