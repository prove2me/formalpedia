-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:35.727442+00:00
-- url     : https://prove2.me/theorems/0dd5a5ae-09b2-4d1b-98c0-7471d8f95efc
-- title:
--   Formal Family Constant Coeff Zero Zero Second Var
-- statement:
--   Definitions and structural lemmas for Formal Family Constant Coeff Zero Zero Second Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalFamilyConstantCoeffZeroZeroSecondVar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
def JM : Matrix (Fin d) (Fin d) (PS k 1 d) := Matrix.of (Jac G)
def Om : Matrix (Fin d) (Fin d) (PS k 1 d) := (JM G)⁻¹
end GlobalTheory.FormalLog


