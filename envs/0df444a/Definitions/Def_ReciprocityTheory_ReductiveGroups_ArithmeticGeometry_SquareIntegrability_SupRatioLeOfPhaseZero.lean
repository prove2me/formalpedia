-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:39:05.703801+00:00
-- url     : https://prove2.me/theorems/fa433db3-7321-4387-9dd8-a282df36e50f
-- title:
--   Sup Ratio Le Of Phase Zero
-- statement:
--   Definitions and structural lemmas for Sup Ratio Le Of Phase Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SupRatioLeOfPhaseZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
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
namespace PT
variable (X : PT E)
def toGT : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := fun x hx => by
    rcases X.eps_pm x hx with h | h <;> simp [h]
def col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : Vsp X.dim → ℂ := fun v => s fun _ => v
end PT
end
end ReciprocityTheory.ChartRestriction.G.I2


