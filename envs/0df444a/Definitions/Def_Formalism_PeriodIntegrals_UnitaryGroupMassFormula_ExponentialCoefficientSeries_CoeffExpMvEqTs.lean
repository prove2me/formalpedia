-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:27.560324+00:00
-- url     : https://prove2.me/theorems/30fde76b-cb3d-499e-bfd5-587acab151e3
-- title:
--   Coeff Exp Mv Eq Ts
-- statement:
--   Definitions and structural lemmas for Coeff Exp Mv Eq Ts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
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
open MvPowerSeries
namespace PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
def ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n
end PI.UnitaryGroupMassFormula.SimeqPdInt


