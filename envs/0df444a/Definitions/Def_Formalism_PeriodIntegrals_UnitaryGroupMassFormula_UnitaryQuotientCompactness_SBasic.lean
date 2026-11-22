-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:43.363296+00:00
-- url     : https://prove2.me/theorems/0fac832f-344f-4205-aa05-e03b275c5d85
-- title:
--   SBasic
-- statement:
--   Definitions and structural lemmas for SBasic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SBasic.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
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
def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩
def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end PI.QuotSetU.UnitaryGroupMassFormula.SW


