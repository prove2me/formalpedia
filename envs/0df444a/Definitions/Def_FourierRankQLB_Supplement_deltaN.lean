-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_deltaN
-- name    : FourierRankQLB_Supplement_deltaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:19:14.613194+00:00
-- url     : https://prove2.me/theorems/01f23d16-20f9-4fb0-832d-5d61ff275ebb
-- title:
--   The tolerance $\delta_n = n^2\,\delta_{0,n}$ (Theorem 7.10)
-- statement:
--   For an ambient dimension $n$, the tolerance of the approximately feasible family of Theorem 7.10 is
--
--   $$
--   \delta_n = n^2\,\delta_{0,n} = n^2\gamma\,\bar g_n^2 ,
--   $$
--
--   the unscaled tolerance multiplied by the scale $s = n^2$. It is $\Theta(n^{-2})$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 7.10, p.44 (with Eq. (91), p.43)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_delta0N

namespace FourierRankQLB

namespace Supplement

/-- The tolerance `δ_n = n² δ_{0,n}` of Theorem 7.10.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 7.10, p. 44. -/
noncomputable def deltaN (n : ℕ) : ℝ := (n : ℝ) ^ 2 * delta0N n

end Supplement

end FourierRankQLB


