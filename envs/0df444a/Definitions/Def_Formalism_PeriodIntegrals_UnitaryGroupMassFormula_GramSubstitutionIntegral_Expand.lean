-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_Expand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:31.209515+00:00
-- url     : https://prove2.me/theorems/31a9a519-57de-45b9-b4be-b6fd9cf18e03
-- title:
--   Expand
-- statement:
--   Definitions and structural lemmas for Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramSubstitutionIntegral/Expand.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
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
namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW
open PI.FglGram PI.UnitaryGroupMassFormula.PhGram
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}
def rhsBy (l ex ph : PowerSeries ℂ_[p]) {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ j', (phAt ph (a j') + ∑ j, if j < j' then be l ex ph (a j) (a j') else 0)
end PI.UnitaryGroupMassFormula.PhGram.ExpandW
namespace PI.UnitaryGroupMassFormula.PhGram
end PI.UnitaryGroupMassFormula.PhGram


