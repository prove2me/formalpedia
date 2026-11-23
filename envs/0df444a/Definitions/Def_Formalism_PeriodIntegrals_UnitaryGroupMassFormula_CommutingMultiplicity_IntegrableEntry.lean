-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:34.746851+00:00
-- url     : https://prove2.me/theorems/6516067d-38fc-4dc8-8544-3f2a2fed13e1
-- title:
--   Integrable Entry
-- statement:
--   Definitions and structural lemmas for Integrable Entry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CommutingMultiplicity/IntegrableEntry.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.CommMult
open MeasureTheory Matrix
section Integral
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
def mInt (μ : Measure H) {m n : Type} (F : H → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ h, F h i j ∂μ
end Integral
end PI.UnitaryGroupMassFormula.CommMult


