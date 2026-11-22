-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:53.909251+00:00
-- url     : https://prove2.me/theorems/6e64dbb7-c5e9-45b8-943a-474d7e88450c
-- title:
--   Mul Vec Bvec Apply
-- statement:
--   Definitions and structural lemmas for Mul Vec Bvec Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/MulVecBvecApply.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
def inW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
end PI.QuotSetU.UnitaryGroupMassFormula.SW


