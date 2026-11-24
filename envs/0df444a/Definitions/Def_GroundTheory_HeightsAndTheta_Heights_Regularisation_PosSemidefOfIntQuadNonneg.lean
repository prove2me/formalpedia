-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:49.279461+00:00
-- url     : https://prove2.me/theorems/8e5a1aa2-2a75-479f-a7f6-47be5b039749
-- title:
--   Pos Semidef Of Int Quad Nonneg
-- statement:
--   Definitions and structural lemmas for Pos Semidef Of Int Quad Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
end PeriodPolydisc
end
end GroundTheory.Heights₂.Heights.Regular


