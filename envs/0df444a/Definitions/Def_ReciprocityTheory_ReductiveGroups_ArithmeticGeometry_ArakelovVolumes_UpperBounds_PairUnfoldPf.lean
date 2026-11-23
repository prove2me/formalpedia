-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:41.52781+00:00
-- url     : https://prove2.me/theorems/537acec2-fd28-4871-bf77-099835f44279
-- title:
--   Pair Unfold Pf
-- statement:
--   Definitions and structural lemmas for Pair Unfold Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Gu (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℂ :=
  X.dom.indicator P x * (starRingEnd ℂ) (X.dom.indicator f0 x) * ((W x).toReal : ℂ)
def phi0 (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (‖X.dom.indicator f0 x‖ ^ 2) * W x
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf


