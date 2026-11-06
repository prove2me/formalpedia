-- Prove2me | Definitions.Def_FourierRankQLB_gd
-- name    : FourierRankQLB_gd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:21.952054+00:00
-- url     : https://prove2.me/theorems/942d487a-60b1-461e-9110-546521c880b1
-- title:
--   The spectral scale $g_d=(1-\cos(\alpha/d))/2$
-- statement:
--   The spectral scale
--   $$
--   g_d=\frac{1-\cos(\alpha/d)}{2},\qquad \alpha=\frac{\pi}{100}.
--   $$
--   It is of order $d^{-2}$ and fixes the spectral shift in the hard matrices $A_Q$.
--
--   **Formalization Note** Every use has $d\ge2$, where the division is genuine.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (25), p.21

import Mathlib
import Definitions.Def_FourierRankQLB_alpha

namespace FourierRankQLB

/-- The spectral scale `g_d = (1 - cos(α/d))/2` of Eq. (25).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (25), p. 21.

**Formalization Note.** At `d = 0` the division gives `α/0 = 0`, so `gd 0 = 0`. Every use has
`d ≥ 2`. -/
noncomputable def gd (d : ℕ) : ℝ := (1 - Real.cos (alpha / d)) / 2

end FourierRankQLB


