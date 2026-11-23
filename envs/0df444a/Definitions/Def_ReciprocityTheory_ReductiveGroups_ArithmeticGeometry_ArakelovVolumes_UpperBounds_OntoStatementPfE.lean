-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:28.9858+00:00
-- url     : https://prove2.me/theorems/d6ebebb5-cad7-4b5b-8722-910a7744547f
-- title:
--   Onto Statement Pf E
-- statement:
--   Definitions and structural lemmas for Onto Statement Pf E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OntoStatementPfE.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open Classical in

def phiF (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) : Frame X.Ψ r → ℝ≥0∞ :=
  fun y => X.dom.piecewise (fun y => ENNReal.ofReal (‖f0 y‖ ^ 2)) 0 y * W y
variable (x0 : Frame X.Ψ r)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE


