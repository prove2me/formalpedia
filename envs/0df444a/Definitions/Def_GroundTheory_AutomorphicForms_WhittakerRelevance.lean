-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
-- name    : GroundTheory_AutomorphicForms_WhittakerRelevance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:24.868948+00:00
-- url     : https://prove2.me/theorems/10fdae64-d444-4d6c-bd41-006d84357dca
-- title:
--   Whittaker Relevance
-- statement:
--   Definitions and structural lemmas for Whittaker Relevance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}
end Whittaker
end GroundTheory.Automorphic


