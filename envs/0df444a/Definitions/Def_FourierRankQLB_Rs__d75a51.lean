-- Prove2me | Definitions.Def_FourierRankQLB_Rs__d75a51
-- name    : FourierRankQLB_Rs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:52.985469+00:00
-- url     : https://prove2.me/theorems/d75a5150-b675-41bc-9d9c-60a9c07c332f
-- title:
--   The outer radius $R_s=s/\sqrt{a_d}$
-- statement:
--   For a scale $s$ and $d=d_n$, the outer radius of the hard ellipsoids,
--   $$
--   R_s=\frac{s}{\sqrt{2g_d}}=\frac{s}{\sqrt{a_d}}.
--   $$
--   It is the radius $R$ an optimizer is given in the oracle model (3), and the ratio $R_s/r_s$ enters the tolerance (54).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (39), p.25 and §5.1, p.30

import Mathlib
import Definitions.Def_FourierRankQLB_ad
import Definitions.Def_FourierRankQLB_dn

namespace FourierRankQLB

/-- The outer radius `R_s = s/√(2g_d) = s/√a_d`, `d = d_n`, of the hard ellipsoids.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (39), p. 25 and §5.1, p. 30.

**Formalization Note.** `a_d > 0` for `d ≥ 2`, so the division is genuine wherever the paper uses
it. -/
noncomputable def Rs (n : ℕ) (s : ℝ) : ℝ := s / √(ad (dn n))

end FourierRankQLB


