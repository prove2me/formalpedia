-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumBoundedBelow
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumBoundedBelow
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:54:10.043725+00:00
-- url     : https://prove2.me/theorems/9982cb4f-0472-4af1-8fc6-b505ec8386d6
-- title:
--   First Minimum Bounded Below
-- statement:
--   Definitions and structural lemmas for First Minimum Bounded Below, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumBoundedBelow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
namespace GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def leviCol (X : Data E 2) (x0 : Frame X.Ψ 2) (τ : X.Ψ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((Real.log (colSq (cpt X x0 w) τ) : ℝ) : ℂ)) z ξ).re
def idF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![1, 0], ![0, 1]]
def swF (Ψ : Finset (E →+* ℂ)) : Frame Ψ 2 := fun _ => ![![0, 1], ![1, 0]]
end GlobalTheory.TwoLines


