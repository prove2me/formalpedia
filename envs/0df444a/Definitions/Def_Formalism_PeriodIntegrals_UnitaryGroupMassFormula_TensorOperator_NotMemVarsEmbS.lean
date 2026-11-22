-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:16.038392+00:00
-- url     : https://prove2.me/theorems/17de1bf8-03cc-462e-96c9-3f4ff781c149
-- title:
--   Not Mem Vars Emb S
-- statement:
--   Definitions and structural lemmas for Not Mem Vars Emb S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/NotMemVarsEmbS.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
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
namespace PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}
end PI.TOW.LiftW


