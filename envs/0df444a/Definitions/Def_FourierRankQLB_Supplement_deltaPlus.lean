-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_deltaPlus
-- name    : FourierRankQLB_Supplement_deltaPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:16:52.625192+00:00
-- url     : https://prove2.me/theorems/7a7697bc-0bc5-498c-9ea8-25f0fbcfe378
-- title:
--   The gap constant $\Delta_+ = \sqrt{2/5} - 1/\sqrt3$ (Eq. (89))
-- statement:
--   The positive constant
--
--   $$
--   \Delta_+ = \sqrt{\tfrac25} - \frac{1}{\sqrt3}
--   $$
--
--   of Eq. (89): the gap, after factoring out $1/\sqrt{\bar g_n}$, between the upper bound on the maximum objective value on the positive regular component and the threshold (81).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (89), p.43

import Mathlib

namespace FourierRankQLB

namespace Supplement

/-- The gap constant `Δ₊ = √(2/5) - 1/√3` of Eq. (89).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (89), p. 43. -/
noncomputable def deltaPlus : ℝ := √(2 / 5) - 1 / √3

end Supplement

end FourierRankQLB


