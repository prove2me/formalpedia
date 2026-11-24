-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:59.350618+00:00
-- url     : https://prove2.me/theorems/7f812362-c77c-4668-9c9d-a6be9cfa5abf
-- title:
--   Frame Meas Statement Pf B
-- statement:
--   Definitions and structural lemmas for Frame Meas Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def SR (R0 : ℝ) : Set (UpI X.Ψ r → ℂ) := {c | ∀ i, ‖c i‖ ≤ R0}
def KR (R0 : ℝ) : ℝ≥0∞ := ∫⁻ y in SR X R0, ENNReal.ofReal (Complex.normSq (jacU y))
def Jp (C : Set (Frame X.Ψ r)) (p : Frame X.Ψ r) : ℝ≥0∞ :=
  ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul p (UF X y)) else 0)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM


