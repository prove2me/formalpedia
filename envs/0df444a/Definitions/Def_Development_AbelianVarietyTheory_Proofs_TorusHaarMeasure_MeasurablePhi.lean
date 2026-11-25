-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:37.264149+00:00
-- url     : https://prove2.me/theorems/0519e669-a96e-444a-b662-3db3508a7694
-- title:
--   Measurable Phi
-- statement:
--   Definitions and structural lemmas for Measurable Phi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)
noncomputable def phi (n : ℕ) (h : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (X.dom.indicator (fun x => X.pnorm (Xa.Fp + n • Xa.L) h x ^ 2) x *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) x ^ (-(1 / 2 : ℝ)) *
    X.dom.indicator (fun x => ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) x ^ (-((n : ℝ) - 1 / 2)))
end GlobalTheory.Up.DivInFFPf


