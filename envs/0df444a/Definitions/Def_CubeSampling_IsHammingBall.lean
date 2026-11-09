-- Prove2me | Definitions.Def_CubeSampling_IsHammingBall
-- name    : CubeSampling_IsHammingBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:28.275925+00:00
-- url     : https://prove2.me/theorems/8c0c17c8-18e5-4fdb-9c32-7dcbd736d7d7
-- title:
--   Hamming ball in $\{-1,1\}^d$
-- statement:
--   A set $E \subseteq \{-1,1\}^d$ is a **Hamming ball** if $E = \{x : d_H(x, c) \le r\}$ for some center $c$ and radius $r \in \mathbb N$, where $d_H$ counts the coordinates in which two points differ. The sets $\{S_d \ge u\}$ are Hamming balls around the all-ones point.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.9, p.6

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- A set of cube points is a Hamming ball: `{x : d_H(x, c) ≤ r}` for a center `c` and a radius `r`
(Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.9, p.6). -/
def IsHammingBall {d : ℕ} (E : Set (Cube d)) : Prop :=
  ∃ (c : Cube d) (r : ℕ), E = {x | hammingDist x c ≤ r}

end CubeSampling


