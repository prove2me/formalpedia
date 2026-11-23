-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_IsExpIntegralParallelogramOfNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:09.784433+00:00
-- url     : https://prove2.me/theorems/9608c8dc-a268-4762-b829-f06d54a0b71c
-- title:
--   Is Exp Integral Parallelogram Of Ne
-- statement:
--   Definitions and structural lemmas for Is Exp Integral Parallelogram Of Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/IsExpIntegralParallelogramOfNe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
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
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ τ : Type*}
section
variable {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
  (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.constantCoeff l = 0)
end
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram


