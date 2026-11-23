-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_StarSingleOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_StarSingleOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:37.820491+00:00
-- url     : https://prove2.me/theorems/71a98341-bf80-407a-9299-bc9a0a61bc15
-- title:
--   Star Single One
-- statement:
--   Definitions and structural lemmas for Star Single One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BoundarySlices/StarSingleOne.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
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
namespace PI.HermitianEmbeddingSlice
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
variable {k r : ℕ}
end PI.HermitianEmbeddingSlice


