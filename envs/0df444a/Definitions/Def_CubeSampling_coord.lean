-- Prove2me | Definitions.Def_CubeSampling_coord
-- name    : CubeSampling_coord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:03.706724+00:00
-- url     : https://prove2.me/theorems/a448cfed-73c3-4ce8-83be-2a61d1cd21fa
-- title:
--   Coordinate $x_i \in \{-1,1\}$ of a cube point
-- statement:
--   For a point $x$ of the Boolean cube $\{-1,1\}^d$ and an index $i \in \{1,\dots,d\}$, the **coordinate** $x_i \in \{-1, 1\}$ is the real number $1$ or $-1$ carried by $x$ at position $i$.
--
--   **Formalization Note** $x_i = 1$ when the Boolean entry is `true` and $x_i = -1$ when it is `false`.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The `i`-th coordinate `x_i ∈ {−1, 1}` of a cube point (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3):
`x_i = 1` when `x i = true` and `x_i = −1` when `x i = false`. -/
def coord {d : ℕ} (x : Cube d) (i : Fin d) : ℝ := if x i then 1 else -1

end CubeSampling


