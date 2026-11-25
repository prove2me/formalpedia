-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:54:44.717474+00:00
-- url     : https://prove2.me/theorems/6bdca60f-3eee-4ab6-8382-0935d64782d9
-- title:
--   Bad Primes Finite
-- statement:
--   Definitions and structural lemmas for Bad Primes Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/BadPrimesFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
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
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
end
end GroundTheory.Global


