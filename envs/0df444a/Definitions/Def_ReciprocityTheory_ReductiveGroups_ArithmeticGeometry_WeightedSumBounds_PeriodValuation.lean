-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:44.062026+00:00
-- url     : https://prove2.me/theorems/0419f0b3-ebeb-443d-9660-ef40469fb8f0
-- title:
--   Period Valuation
-- statement:
--   Definitions and structural lemmas for Period Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
section Coeff
variable {K : Type*} [Field K]
end Coeff
section Val
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
end Val
section ZetaNonvanishing₂
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
end ZetaNonvanishing₂
end
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps


