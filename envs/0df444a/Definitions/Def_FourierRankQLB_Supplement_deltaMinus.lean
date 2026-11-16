-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_deltaMinus
-- name    : FourierRankQLB_Supplement_deltaMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:17:07.681402+00:00
-- url     : https://prove2.me/theorems/e1040a08-db26-4f2c-ae99-353f16303c91
-- title:
--   The gap constant $\Delta_- = (3 - 2\sqrt2)/\sqrt{20}$ (Eq. (89))
-- statement:
--   The positive constant
--
--   $$
--   \Delta_- = \frac{3 - 2\sqrt2}{\sqrt{20}}
--   $$
--
--   of Eq. (89): the gap, after factoring out $1/\sqrt{\bar g_n}$, between the threshold (81) and the lower bound on the maximum objective value on the negative regular component after inverse iteration.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (89), p.43

import Mathlib

namespace FourierRankQLB

namespace Supplement

/-- The gap constant `Δ₋ = (3 - 2√2)/√20` of Eq. (89).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (89), p. 43. -/
noncomputable def deltaMinus : ℝ := (3 - 2 * √2) / √20

end Supplement

end FourierRankQLB


