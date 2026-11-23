-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCountHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCountHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:51.134825+00:00
-- url     : https://prove2.me/theorems/ece9e4d5-8fdc-4c3c-ba7c-582aa84ec7bf
-- title:
--   Hensel Count Holds
-- statement:
--   Definitions and structural lemmas for Hensel Count Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/HenselCountHolds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_HenselCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS
open MeasureTheory Topology
section Hensel
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}
end Hensel
end PI.VolStabS


