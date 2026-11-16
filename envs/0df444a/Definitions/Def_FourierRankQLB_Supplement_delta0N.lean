-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_delta0N
-- name    : FourierRankQLB_Supplement_delta0N
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:18:24.088009+00:00
-- url     : https://prove2.me/theorems/71f9fc40-bdc6-47db-b81f-b0324646bcc1
-- title:
--   The unscaled tolerance $\delta_{0,n} = \gamma\,\bar g_n^2$ (Eq. (91))
-- statement:
--   For an ambient dimension $n$, with $\bar g_n = g_{d_n}$ (Eq. (37)), the unscaled tolerance of the approximately feasible reduction is
--
--   $$
--   \delta_{0,n} = \gamma\, \bar g_n^{2},
--   $$
--
--   Eq. (91). It is $\Theta(n^{-4})$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (91), p.43 (with Eq. (37), p.25)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_gammaStar
import Definitions.Def_FourierRankQLB_gd
import Definitions.Def_FourierRankQLB_dn

namespace FourierRankQLB

namespace Supplement

/-- The unscaled tolerance `δ_{0,n} = γ ḡ_n²` of Eq. (91), with `ḡ_n = g_{d_n}` (Eq. (37)).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (91), p. 43 (and Eq. (37), p. 25). -/
noncomputable def delta0N (n : ℕ) : ℝ := gammaStar * gd (dn n) ^ 2

end Supplement

end FourierRankQLB


