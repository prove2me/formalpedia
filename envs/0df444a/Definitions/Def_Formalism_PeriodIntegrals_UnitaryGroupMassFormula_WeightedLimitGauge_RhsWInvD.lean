-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:25.147424+00:00
-- url     : https://prove2.me/theorems/ba4cfc7a-5af0-5e15-859c-43ae09b90881
-- title:
--   Rhs WInv D
-- statement:
--   Definitions and structural lemmas for Rhs WInv D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvD.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
import Theorems.Thm_PI_RhsWLim_W_HU_amb_closed
import Theorems.Thm_PI_RhsWLim_W_RI_inv_fix

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
open PI.RhsWLim PI.RhsWLim.W
variable {k r : ℕ}
instance : T2Space (HU.Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ HU.amb k r})
instance : LocallyCompactSpace (HU.Gp k r) :=
  show LocallyCompactSpace {x : Mt k r // x ∈ HU.amb k r} from
    HU.amb_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
def stabH (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Subgroup (HU.Gp k r) where
  carrier := {g | Matrix.of (HU.inc g) *ᵥ z' = z'}
  mul_mem' {a b} ha hb := by
    show (Matrix.of (HU.inc a) * Matrix.of (HU.inc b) : Mat k r) *ᵥ z' = z'
    rw [← Matrix.mulVec_mulVec]
    rw [show Matrix.of (HU.inc b) *ᵥ z' = z' from hb]
    exact ha
  one_mem' := by
    show (1 : Mat k r) *ᵥ z' = z'
    exact Matrix.one_mulVec z'
  inv_mem' {a} ha := by
    show (Matrix.of (HU.inc a) : Mat k r)⁻¹ *ᵥ z' = z'
    exact inv_fix (HU.uwb_unit (HU.inc_mem a)) ha
def jH (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Mt k r := HU.inc h.1
end PI.RhsWLim.W.RI


