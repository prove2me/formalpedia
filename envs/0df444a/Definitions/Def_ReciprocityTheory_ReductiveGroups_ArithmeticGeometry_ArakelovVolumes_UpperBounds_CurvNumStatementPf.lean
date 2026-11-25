-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CurvNumStatementPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CurvNumStatementPf
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:13:40.693802+00:00
-- url     : https://prove2.me/theorems/c528c7f5-bae2-568d-b091-b5723bec8e79
-- title:
--   Curv Num Statement Pf
-- statement:
--   Definitions and structural lemmas for Curv Num Statement Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CurvNumStatementPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def coefR {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (τ : X.Ψ) (a j : Fin r) : ℝ :=
  Dsg X j / Dsg X a * (v τ a - v τ j)
end ReciprocityTheory.ChartRestriction.G.AR.Up


