-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
-- name    : GroundTheory_PAdicHodge_PerfectoidCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:05.641194+00:00
-- url     : https://prove2.me/theorems/06767e30-ba86-42a9-aa65-512d36657f86
-- title:
--   Perfectoid Criterion
-- statement:
--   Definitions and structural lemmas for Perfectoid Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCriterion.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
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
namespace IsPerfectoidField
section Norm
variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)
end Norm
section Perfectoid
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
end Perfectoid
end IsPerfectoidField
end GroundTheory.PAdicHodge


