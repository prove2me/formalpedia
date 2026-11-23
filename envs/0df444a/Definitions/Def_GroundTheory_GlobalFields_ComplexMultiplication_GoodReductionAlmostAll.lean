-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:05.21628+00:00
-- url     : https://prove2.me/theorems/3845edd9-0d41-41d4-b4a5-fa46806c2b0f
-- title:
--   Good Reduction Almost All
-- statement:
--   Definitions and structural lemmas for Good Reduction Almost All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/GoodReductionAlmostAll.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
end
end GroundTheory.Global


