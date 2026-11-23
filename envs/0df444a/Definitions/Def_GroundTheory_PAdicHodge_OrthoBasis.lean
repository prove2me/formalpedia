-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
-- name    : GroundTheory_PAdicHodge_OrthoBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:20.928803+00:00
-- url     : https://prove2.me/theorems/aa8aff0e-4ac9-4432-80fe-9bfc1d68a48d
-- title:
--   Ortho Basis
-- statement:
--   Definitions and structural lemmas for Ortho Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/OrthoBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
variable [CompleteSpace k]
end GroundTheory.PAdicHodge


