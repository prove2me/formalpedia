-- Prove2me | Definitions.Def_CubeSampling_HasExactDegree
-- name    : CubeSampling_HasExactDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:18:00.956409+00:00
-- url     : https://prove2.me/theorems/241fed19-5df9-478b-8b60-993760fe36e6
-- title:
--   Exact degree $\ell$
-- statement:
--   A function $p$ on $\{-1,1\}^D$ has **exact degree $\ell$** if $p \in P_{D,\ell}$ and $p \notin P_{D,j}$ for every $j < \ell$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 4.2, p.17

import Mathlib
import Definitions.Def_CubeSampling_lowDeg

namespace CubeSampling

/-- `p` has exact degree `ℓ` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 4.2, p.17): `p ∈ P_{D,ℓ}` and `p ∉ P_{D,j}` for every `j < ℓ`. -/
def HasExactDegree (D ℓ : ℕ) (p : Cube D → ℝ) : Prop := p ∈ lowDeg D ℓ ∧ ∀ j < ℓ, p ∉ lowDeg D j

end CubeSampling


