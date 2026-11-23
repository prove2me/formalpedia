-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:43.355799+00:00
-- url     : https://prove2.me/theorems/d48b6cae-1c1b-4d01-9026-e6bbde066976
-- title:
--   Elliptic Constant
-- statement:
--   Definitions and structural lemmas for Elliptic Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {E : Type*} [NormedAddCommGroup E]
def limPunctured (f : ℂ → E) (z : ℂ) : E := limUnder (𝓝[≠] z) f
variable [NormedSpace ℂ E]
variable {L : PeriodPair}
end Elliptic
end GroundTheory.Global


