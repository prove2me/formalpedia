-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:53.549431+00:00
-- url     : https://prove2.me/theorems/ac00941c-61d0-4152-8b46-6c966022ee24
-- title:
--   Nilpotent Subgroup
-- statement:
--   Definitions and structural lemmas for Nilpotent Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/NilpotentSubgroup.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
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
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}
def NC (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0
end PI.QuotSetU.UnitaryGroupMassFormula.SW


