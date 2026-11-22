-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:38.742925+00:00
-- url     : https://prove2.me/theorems/d2a6a2b1-6eb3-4bb4-b8c3-649398d9e3ba
-- title:
--   Unitary Weyl Compact
-- statement:
--   Definitions and structural lemmas for Unitary Weyl Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/UnitaryWeylCompact.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
def lI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
def Wp (k r : ℕ) : Finset (Fin (2 * r + k + 1)) :=
  Finset.univ.filter fun i => r ≤ i.val ∧ i.val < r + k
def Bd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ((2 * r + k + 1 : ℕ) : ℝ) +
    (Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2) * ((2 * r + k + 1 : ℕ) : ℝ) + ∑ i, ‖z i‖) /
      (‖z (lI k r)‖ - Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2))
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.UWC
end PI.QuotSetU.UnitaryGroupMassFormula
end


