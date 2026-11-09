-- Prove2me | Definitions.Def_CubeSampling_tauR
-- name    : CubeSampling_tauR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:30.739195+00:00
-- url     : https://prove2.me/theorems/92c8c81d-260d-49fe-b982-229505b39efd
-- title:
--   Center $\tau_R = 2\sqrt{(k-R)(d-k-R)}$
-- statement:
--   For $0 \le R \le k$,
--   $$
--   \tau_R = 2\sqrt{(k-R)(d-k-R)},
--   $$
--   the smallest center of the one-dimensional constructions used in the harmonic lift with harmonic degrees up to $R$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 5.1, p.20

import Mathlib

namespace CubeSampling

/-- The center `τ_R = 2 √((k − R)(d − k − R))` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §5.1, p.20), in real arithmetic. -/
noncomputable def tauR (d k R : ℕ) : ℝ := 2 * Real.sqrt (((k : ℝ) - R) * ((d : ℝ) - k - R))

end CubeSampling


