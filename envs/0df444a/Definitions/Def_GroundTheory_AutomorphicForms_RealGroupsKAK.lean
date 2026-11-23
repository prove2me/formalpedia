-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
-- name    : GroundTheory_AutomorphicForms_RealGroupsKAK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:36.945223+00:00
-- url     : https://prove2.me/theorems/1bb32061-24af-4319-becc-0408500b123a
-- title:
--   Real Groups KAK
-- statement:
--   Definitions and structural lemmas for Real Groups KAK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsKAK.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Matrix Polynomial
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
end GroundTheory.Automorphic


