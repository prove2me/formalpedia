-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:54.657527+00:00
-- url     : https://prove2.me/theorems/6c610fbf-4d49-424e-abce-3fbe97f4c09d
-- title:
--   Ext FStatement Pf
-- statement:
--   Definitions and structural lemmas for Ext FStatement Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExtFStatementPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
def chartE (X : Data E r) : Frame X.Ψ r ≃L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r)) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin).symm
variable {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open scoped ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end ReciprocityTheory.ChartRestriction.G.AR.Up


