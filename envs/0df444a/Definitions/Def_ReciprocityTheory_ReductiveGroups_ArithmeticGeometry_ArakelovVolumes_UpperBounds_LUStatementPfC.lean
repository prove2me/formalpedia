-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:57.524951+00:00
-- url     : https://prove2.me/theorems/7bb6932d-f7f7-45c4-b814-262832a6e4d4
-- title:
--   LUStatement Pf C
-- statement:
--   Definitions and structural lemmas for LUStatement Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LUStatementPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}
def cellL (X : Data E r) (x0 : Frame X.Ψ r) : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ DeltaF X x0 x ≠ 0}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf


