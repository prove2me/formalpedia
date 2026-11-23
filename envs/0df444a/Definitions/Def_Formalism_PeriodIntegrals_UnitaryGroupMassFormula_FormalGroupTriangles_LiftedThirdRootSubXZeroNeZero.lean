-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:30.623796+00:00
-- url     : https://prove2.me/theorems/e4ae69e5-00eb-4a78-a590-7cd188c7f11d
-- title:
--   Lifted Third Root Sub XZero Ne Zero
-- statement:
--   Definitions and structural lemmas for Lifted Third Root Sub XZero Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
def Lab (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (lam wq)
def Lac (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 2) (lam wq)
def s3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (Z3 W wq)
end PI.FglTriFactor.Wk


