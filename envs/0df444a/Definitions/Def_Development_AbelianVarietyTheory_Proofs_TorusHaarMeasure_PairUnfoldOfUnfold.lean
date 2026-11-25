-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PairUnfoldOfUnfold
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PairUnfoldOfUnfold
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:18.905253+00:00
-- url     : https://prove2.me/theorems/6c983b01-c4ec-43e0-bf22-acd57f835b67
-- title:
--   Pair Unfold Of Unfold
-- statement:
--   Definitions and structural lemmas for Pair Unfold Of Unfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PairUnfoldOfUnfold.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.PairUnfold
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open Classical in

def pairDens {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) :
    Frame X.Ψ r → ℂ :=
  fun y => X.dom.piecewise (fun y => P y * (starRingEnd ℂ) (f0 y)) 0 y * ((W y).toReal : ℂ)
end
end GlobalTheory.PairUnfold


