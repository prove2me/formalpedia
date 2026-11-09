-- Prove2me | Definitions.Def_CubeSampling_IsRadial
-- name    : CubeSampling_IsRadial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:42.928875+00:00
-- url     : https://prove2.me/theorems/9557bc3a-25ee-4e15-9a53-2a5e0e50f917
-- title:
--   Radial function on $\{-1,1\}^D$
-- statement:
--   A function $p$ on $\{-1,1\}^D$ is **radial** if it depends only on the coordinate sum: $p(x) = g(S_D(x))$ for some $g : \mathbb Z \to \mathbb R$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 2.3, p.9; Section 4, p.15

import Mathlib
import Definitions.Def_CubeSampling_coordSum

namespace CubeSampling

/-- A function on `{−1, 1}^D` is radial if it depends only on the coordinate sum `S_D`
(Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §2.3, p.9 and §4, p.15). -/
def IsRadial (D : ℕ) (p : Cube D → ℝ) : Prop := ∃ g : ℤ → ℝ, ∀ x, p x = g (coordSum D x)

end CubeSampling


