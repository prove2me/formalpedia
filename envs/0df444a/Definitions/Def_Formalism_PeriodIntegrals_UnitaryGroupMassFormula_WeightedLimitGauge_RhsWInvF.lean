-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:28.407239+00:00
-- url     : https://prove2.me/theorems/c73b3a03-3ce0-502b-aaf8-adab3e70d971
-- title:
--   Rhs WInv F
-- statement:
--   Definitions and structural lemmas for Rhs WInv F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvF.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
namespace PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ}
section Form
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
def tmat (κ : ℂ) (d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.of fun i j => κ * d i * (star d ᵥ* H) j
end Form
end PI.RhsWLim.W.RI


