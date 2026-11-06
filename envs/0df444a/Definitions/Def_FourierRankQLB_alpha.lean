-- Prove2me | Definitions.Def_FourierRankQLB_alpha
-- name    : FourierRankQLB_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:41.623228+00:00
-- url     : https://prove2.me/theorems/b9fb2234-6cf7-4398-86f1-42a516bc676a
-- title:
--   The constant $\alpha=\pi/100$
-- statement:
--   The constant
--   $$
--   \alpha=\frac{\pi}{100}.
--   $$
--   It sets the width of the interval near $\pi$ in which few eigenangles fall, and hence the spectral scale $g_d$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (25), p.21

import Mathlib

namespace FourierRankQLB

/-- The constant `α = π/100` of Eq. (25).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (25), p. 21. -/
noncomputable def alpha : ℝ := Real.pi / 100

end FourierRankQLB


