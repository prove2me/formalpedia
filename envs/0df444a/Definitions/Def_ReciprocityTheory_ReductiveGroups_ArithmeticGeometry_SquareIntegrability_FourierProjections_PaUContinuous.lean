-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:29.590728+00:00
-- url     : https://prove2.me/theorems/a57427c6-ecfd-4c2b-b3f3-7d429d5a4203
-- title:
--   Pa UContinuous
-- statement:
--   Definitions and structural lemmas for Pa UContinuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
def paK (q c : ℕ) (u : EuclideanSpace ℂ ι) : ℝ := (1 + ‖u‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖u‖ ^ 2)
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw


