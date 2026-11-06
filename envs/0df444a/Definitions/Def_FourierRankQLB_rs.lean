-- Prove2me | Definitions.Def_FourierRankQLB_rs
-- name    : FourierRankQLB_rs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:50.24022+00:00
-- url     : https://prove2.me/theorems/63b57286-eda1-40cd-a3ab-365f225ceea6
-- title:
--   The inner radius $r_s=s/\sqrt{1+a_d}$
-- statement:
--   For a scale $s$ and $d=d_n$, the inner radius of the hard ellipsoids,
--   $$
--   r_s=\frac{s}{\sqrt{1+2g_d}}=\frac{s}{\sqrt{1+a_d}}.
--   $$
--   It is the radius $r$ an optimizer is given in the oracle model (3).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (39), p.25 and §5.1, p.30

import Mathlib
import Definitions.Def_FourierRankQLB_ad
import Definitions.Def_FourierRankQLB_dn

namespace FourierRankQLB

/-- The inner radius `r_s = s/√(1 + 2g_d) = s/√(1 + a_d)`, `d = d_n`, of the hard ellipsoids.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (39), p. 25 and §5.1, p. 30. -/
noncomputable def rs (n : ℕ) (s : ℝ) : ℝ := s / √(1 + ad (dn n))

end FourierRankQLB


