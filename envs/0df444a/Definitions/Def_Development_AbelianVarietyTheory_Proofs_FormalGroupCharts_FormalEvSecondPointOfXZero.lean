-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:08.700213+00:00
-- url     : https://prove2.me/theorems/ee5ddb6a-f24e-4281-8528-17df4f0fd55d
-- title:
--   Formal Ev Second Point Of XZero
-- statement:
--   Definitions and structural lemmas for Formal Ev Second Point Of XZero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalEvSecondPointOfXZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt

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
def Jac : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))
def Ar : Fin d → Fin d → PS k 2 d := fun i b => pderiv k ((1 : Fin 2), b) (G.F i)
section Fams
end Fams
end GlobalTheory.FormalLog


