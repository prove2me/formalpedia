-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T07:41:42.021071+00:00
-- url     : https://prove2.me/theorems/1e849781-0d43-44f1-82c0-0b6f5fc0fd48
-- title:
--   Uniq Gen
-- statement:
--   Definitions and structural lemmas for Uniq Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/UniqGen.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W
open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
section Gen
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V]
variable [SecondCountableTopology V]
variable [MeasurableSpace V] [BorelSpace V]
end Gen
section Fib
variable {V X Y : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]
variable (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
  (f : V → Y) (ι : X → Y) (U : Set V)
end Fib
end PI.OmFibreUniq.W


