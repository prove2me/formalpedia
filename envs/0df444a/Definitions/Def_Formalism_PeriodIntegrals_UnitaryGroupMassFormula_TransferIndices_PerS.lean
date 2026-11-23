-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:45.178956+00:00
-- url     : https://prove2.me/theorems/2a78efbf-1408-4178-847e-5bd088a55aa5
-- title:
--   Per S
-- statement:
--   Definitions and structural lemmas for Per S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/PerS.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open PI.Dv NumberField
section PerS
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
end PerS
end PI.Dv.TIW


