-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:13.498674+00:00
-- url     : https://prove2.me/theorems/adcf7ede-a0ba-4777-9032-2765c2cf9edd
-- title:
--   Measure Eq Of Cos
-- statement:
--   Definitions and structural lemmas for Measure Eq Of Cos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/MeasureEqOfCos.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_CosDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open MeasureTheory Topology Set Filter
section CosMeas
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
omit [MeasurableSpace X] [OpensMeasurableSpace X] in

def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}
end CosMeas
end PI.VolStabSW


