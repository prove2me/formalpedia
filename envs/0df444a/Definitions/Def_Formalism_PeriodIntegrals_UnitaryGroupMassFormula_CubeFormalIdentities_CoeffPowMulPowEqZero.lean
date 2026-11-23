-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:37.294244+00:00
-- url     : https://prove2.me/theorems/a670b03b-6fa3-40ea-ab17-fefc71698de1
-- title:
--   Coeff Pow Mul Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for Coeff Pow Mul Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubeFormalIdentities/CoeffPowMulPowEqZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
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
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
def Good (D : MvPowerSeries σ ℂ_[p]) : Prop :=
  constantCoeff D = 0 ∧ IntegralMv (expMv D)
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram


