-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:13.638909+00:00
-- url     : https://prove2.me/theorems/f057fab2-0ccf-4af6-9d8e-7b8a5115c1e2
-- title:
--   Ok Smul Right
-- statement:
--   Definitions and structural lemmas for Ok Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/OkSmulRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.TOW
open PI.TO
variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}
end PI.TOW


