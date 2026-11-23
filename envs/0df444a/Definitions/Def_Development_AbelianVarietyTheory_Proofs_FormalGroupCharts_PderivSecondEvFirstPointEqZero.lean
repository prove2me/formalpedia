-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:01.069752+00:00
-- url     : https://prove2.me/theorems/fed0e4bd-e812-4ec0-acbe-cc40cc0d1667
-- title:
--   Pderiv Second Ev First Point Eq Zero
-- statement:
--   Definitions and structural lemmas for Pderiv Second Ev First Point Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
def logOf (i : Fin d) : PS k 1 d := prim (fun v : Fin 1 × Fin d => Om G i v.2)
end GlobalTheory.FormalLog


