-- Prove2me | Definitions.Def_CubeSampling_cubeProb
-- name    : CubeSampling_cubeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:01.392069+00:00
-- url     : https://prove2.me/theorems/a973844b-7741-4b10-9c49-2b7a694befd2
-- title:
--   Probability $\mu_d(E)$ of a set of cube points
-- statement:
--   For a set $E \subseteq \{-1,1\}^d$, its **probability** under the uniform measure is
--   $$
--   \mu_d(E) = \mathbb E[\mathbf 1_E] = \frac{|E|}{2^d} \in [0,1].
--   $$
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.9, p.6

import Mathlib
import Definitions.Def_CubeSampling_cubeMean

namespace CubeSampling

/-- The probability `μ_d(E) = |E| / 2^d` of a set `E` of cube points (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.9, p.6),
as a real number: the mean of the indicator of `E`. -/
noncomputable def cubeProb (d : ℕ) (E : Set (Cube d)) : ℝ := cubeMean d (E.indicator 1)

end CubeSampling


