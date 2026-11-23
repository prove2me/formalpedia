-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:23.647922+00:00
-- url     : https://prove2.me/theorems/c026b9ce-ecd4-4ec0-9786-ad2f8278e3e8
-- title:
--   Pair Subst XZero
-- statement:
--   Definitions and structural lemmas for Pair Subst XZero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
section Ops
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}
end Ops
section Pair
variable {τ : Type*}
def pr (x y : MvPowerSeries τ ℂ_[p]) (f : MvPowerSeries (Fin 2) ℂ_[p]) : MvPowerSeries τ ℂ_[p] :=
  MvPowerSeries.subst ![x, y] f
end Pair
end PI.FglTriFactor.Wk


