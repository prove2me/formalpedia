-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoMeas
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoMeas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:05.51575+00:00
-- url     : https://prove2.me/theorems/ebb4fa3c-da69-4a67-9c7d-b433a99d27a9
-- title:
--   Topo Meas
-- statement:
--   Definitions and structural lemmas for Topo Meas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TopoMeas.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.TopoMeas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
end PI.VolStabSW.TopoMeas
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory PI.VolFromSW
end PI.VolStabSW


