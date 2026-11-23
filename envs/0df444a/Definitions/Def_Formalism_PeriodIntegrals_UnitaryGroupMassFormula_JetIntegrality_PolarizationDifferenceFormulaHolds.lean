-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:14.060736+00:00
-- url     : https://prove2.me/theorems/fdedd3f3-f1eb-4110-9558-615d02708f72
-- title:
--   Polarization Difference Formula Holds
-- statement:
--   Definitions and structural lemmas for Polarization Difference Formula Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/PolarizationDifferenceFormulaHolds.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_TwoUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.JetsPhW.W
open PI.JetsPhW
namespace R
variable {K : Type*} [CommRing K]
end R
section
variable {p : ℕ} [Fact p.Prime] {σ : Type*} {l ex ph : PowerSeries ℂ_[p]}
end
end PI.JetsPhW.W


