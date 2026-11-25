-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:33.206424+00:00
-- url     : https://prove2.me/theorems/5479ae78-5493-4a18-b65d-9b507486a8b9
-- title:
--   Tof Span Condition
-- statement:
--   Definitions and structural lemmas for Tof Span Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def uMap {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Vsp dim →ₗ[ℝ] Vsp dim :=
  (IR I).starProjection.toLinearMap ∘ₗ
    (((-Complex.I) • LinearMap.id : Vsp dim →ₗ[ℂ] Vsp dim).restrictScalars ℝ)
end
end ReciprocityTheory.ChartRestriction.G.I2


