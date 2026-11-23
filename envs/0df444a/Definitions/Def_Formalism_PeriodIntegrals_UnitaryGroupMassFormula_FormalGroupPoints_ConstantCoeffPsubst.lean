-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffPsubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:43.051952+00:00
-- url     : https://prove2.me/theorems/a7cc5660-376d-4d4a-bcda-103fa1725115
-- title:
--   Constant Coeff Psubst
-- statement:
--   Definitions and structural lemmas for Constant Coeff Psubst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupPoints/ConstantCoeffPsubst.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglPtW.Wk
open PI.AddIntG.Wk
variable {K : Type*} [CommRing K]
abbrev law (l ex : PowerSeries K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst
    (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex
abbrev mulSer (l ex : PowerSeries K) (c : K) : MvPowerSeries Unit K :=
  PowerSeries.subst
    (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex
end PI.FglPtW.Wk
end


