-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:25.045286+00:00
-- url     : https://prove2.me/theorems/eb23f66d-fda2-4255-804f-f521a3e781dc
-- title:
--   Ext FStatement Pf B
-- statement:
--   Definitions and structural lemmas for Ext FStatement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExtFStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
def Gf (x : Frame X.Ψ r) : ℝ≥0∞ := ENNReal.ofReal (X.pnorm la (P0 D la F) x ^ 2)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf


