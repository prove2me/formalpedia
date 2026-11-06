-- Prove2me | Definitions.Def_FourierRankQLB_ad
-- name    : FourierRankQLB_ad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:39.004104+00:00
-- url     : https://prove2.me/theorems/9473d2b1-15bd-420b-862c-3a65fafe3139
-- title:
--   The constant $a_d=2g_d=1-\cos(\alpha/d)$
-- statement:
--   The constant
--   $$
--   a_d=2g_d=1-\cos(\alpha/d).
--   $$
--   It is the smallest possible eigenvalue of $A_Q$, and it normalizes the statistic $Z$ and the accuracy thresholds of the main theorem.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (43), p.27

import Mathlib
import Definitions.Def_FourierRankQLB_gd

namespace FourierRankQLB

/-- `a_d = 2 g_d = 1 - cos(α/d)`, Eq. (43).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (43), p. 27. -/
noncomputable def ad (d : ℕ) : ℝ := 2 * gd d

end FourierRankQLB


