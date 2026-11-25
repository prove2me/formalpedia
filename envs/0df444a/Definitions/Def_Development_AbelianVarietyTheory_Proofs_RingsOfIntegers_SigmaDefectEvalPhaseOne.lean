-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:43.916622+00:00
-- url     : https://prove2.me/theorems/6d60c00f-c176-4015-9f2b-a0ba2ab59c7d
-- title:
--   Sigma Defect Eval Phase One
-- statement:
--   Definitions and structural lemmas for Sigma Defect Eval Phase One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/SigmaDefectEvalPhaseOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
end GlobalTheory.SigmaDefect


