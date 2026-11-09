-- Prove2me | Definitions.Def_CubeSampling_coordSum
-- name    : CubeSampling_coordSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:58.060091+00:00
-- url     : https://prove2.me/theorems/27406fa1-a305-40d2-8c02-35f23e666dd6
-- title:
--   Coordinate sum $S_d(x) = x_1 + \dots + x_d$
-- statement:
--   The **coordinate sum** of $x \in \{-1,1\}^d$ is the integer
--   $$
--   S_d(x) = x_1 + \dots + x_d \in \{-d, -d+2, \dots, d\},
--   $$
--   with $S_0 = 0$ on the one-point cube $\{-1,1\}^0$. Radial functions are functions of $S_d$, and the concentration sets of the mission are the Hamming balls $\{S_d \ge u\}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 2.3, p.9; Lemma 5.1, p.19

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The coordinate sum `S_d(x) = x_1 + ⋯ + x_d ∈ ℤ` of a cube point (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §2.3, p.9 and
Lemma 5.1, p.19), with `x_i = 1` for `x i = true` and `x_i = −1` otherwise. `S_0 = 0`. -/
def coordSum (d : ℕ) (x : Cube d) : ℤ := ∑ i, if x i then (1 : ℤ) else -1

end CubeSampling


