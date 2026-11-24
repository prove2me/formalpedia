-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:59.623152+00:00
-- url     : https://prove2.me/theorems/cc21663a-5839-4296-a284-c23c977d7de1
-- title:
--   PLines Ideal Index Pos
-- statement:
--   Definitions and structural lemmas for PLines Ideal Index Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealIndexPos.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
namespace KLinesIdealIndexPos
variable {K : Type} [Field K] [NumberField K]
noncomputable def toOne (K : Type) [Field K] : K →ₗ[𝓞 K] (Unit → K) :=
  LinearMap.pi fun _ => LinearMap.id
end KLinesIdealIndexPos
end GroundTheory.Heights₂.Heights


