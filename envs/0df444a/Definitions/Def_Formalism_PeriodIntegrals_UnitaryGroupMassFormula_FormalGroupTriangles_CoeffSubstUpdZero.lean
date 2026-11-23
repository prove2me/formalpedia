-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:02.983401+00:00
-- url     : https://prove2.me/theorems/71fe5e15-517e-43f9-9492-1ab8299f3716
-- title:
--   Coeff Subst Upd Zero
-- statement:
--   Definitions and structural lemmas for Coeff Subst Upd Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
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
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]
def upd (k : σ) (t : MvPowerSeries σ K) : σ → MvPowerSeries σ K := Function.update MvPowerSeries.X k t
end PI.FglTriFactor.Wk


