-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:14.885514+00:00
-- url     : https://prove2.me/theorems/ccac50cc-75e9-42cf-aafc-6795dece3ab0
-- title:
--   Norm Delta Wc
-- statement:
--   Definitions and structural lemmas for Norm Delta Wc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupChords/NormDeltaWc.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.FglChordFactor.Wk
def Wc : WeierstrassCurve ℂ_[2] := ⟨0, 0, 1, 0, 0⟩
def catC : PowerSeries ℂ_[2] := PowerSeries.map (Nat.castRingHom ℂ_[2]) PowerSeries.catalanSeries
def wqc : PowerSeries ℂ_[2] := PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) catC
end PI.FglChordFactor.Wk


