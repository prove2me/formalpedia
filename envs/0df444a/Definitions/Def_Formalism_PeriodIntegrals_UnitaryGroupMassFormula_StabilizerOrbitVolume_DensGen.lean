-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:18.39623+00:00
-- url     : https://prove2.me/theorems/042c1c26-6209-47ba-a0aa-fa47c99306df
-- title:
--   Dens Gen
-- statement:
--   Definitions and structural lemmas for Dens Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensGen.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
end PI.VolStabSW.DensGen


