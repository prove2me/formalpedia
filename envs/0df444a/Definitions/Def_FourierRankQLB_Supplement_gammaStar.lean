-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_gammaStar
-- name    : FourierRankQLB_Supplement_gammaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:17:40.328267+00:00
-- url     : https://prove2.me/theorems/c9a5b0ee-ff9c-4e22-9a44-8374fd565203
-- title:
--   The constant $\gamma = \min\{1, \rho^2/49, \Delta_+, \Delta_-/3\}$ (Eq. (90))
-- statement:
--   The constant
--
--   $$
--   \gamma = \min\Big\{1,\ \frac{\rho^2}{49},\ \Delta_+,\ \frac{\Delta_-}{3}\Big\}
--   $$
--
--   of Eq. (90), chosen small enough to preserve both gaps $\Delta_\pm$ and the inverse-error bound in the approximately feasible reduction.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (90), p.43

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_rhoStar
import Definitions.Def_FourierRankQLB_Supplement_deltaPlus
import Definitions.Def_FourierRankQLB_Supplement_deltaMinus

namespace FourierRankQLB

namespace Supplement

/-- The constant `γ = min{1, ρ²/49, Δ₊, Δ₋/3}` of Eq. (90).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (90), p. 43. -/
noncomputable def gammaStar : ℝ := min (min 1 (rhoStar ^ 2 / 49)) (min deltaPlus (deltaMinus / 3))

end Supplement

end FourierRankQLB


