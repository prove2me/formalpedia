-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:23.539084+00:00
-- url     : https://prove2.me/theorems/18ef3db7-a453-44dc-8b18-776546b09a80
-- title:
--   Formal Group Law Exists
-- statement:
--   Definitions and structural lemmas for Formal Group Law Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/FormalGroupLawExists.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
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
namespace PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
def bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p] :=
  fun i => if i = 0 then 0 else Z3 W wq
end PI.AddIntG.Wk


