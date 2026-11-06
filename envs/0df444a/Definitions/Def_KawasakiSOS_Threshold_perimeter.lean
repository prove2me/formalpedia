-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_perimeter
-- name    : KawasakiSOS_Threshold_perimeter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:59.894968+00:00
-- url     : https://prove2.me/theorems/60d18330-380a-45a3-b404-c86cb974e618
-- title:
--   The perimeter $p(h)$
-- statement:
--   For a height vector $h:\mathbb Z_k\to\mathbb Z_{\ge0}$, the perimeter of $h$ is
--
--   $$p(h)=\sum_{i\in\mathbb Z_k}\bigl|h(i)-h(i+1)\bigr|.$$
--
--   It measures the length of the vertical boundary of the interface. For $k=2$ the cycle $C_2$ has two parallel edges between columns $0$ and $1$, and the same formula gives $p(h)=2|h(0)-h(1)|$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The perimeter `p(h) = ∑_{i ∈ ℤ_k} |h(i) − h(i+1)|`. Formalization Note: stated for every height vector, not only for `h ∈ Ω`; at `k = 2` the sum runs over both edges of `C_2`, so it equals `2|h(0) − h(1)|` with no special case.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
def perimeter {k : ℕ} [NeZero k] (h : ZMod k → ℕ) : ℕ :=
  ∑ i, ((h i : ℤ) - (h (i + 1) : ℤ)).natAbs

end KawasakiSOS.Threshold


