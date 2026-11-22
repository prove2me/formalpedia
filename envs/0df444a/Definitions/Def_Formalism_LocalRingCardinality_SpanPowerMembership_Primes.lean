-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_Primes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:29.272809+00:00
-- url     : https://prove2.me/theorems/84116cf7-6ec9-4d15-aa5c-631319241f6a
-- title:
--   Primes
-- statement:
--   Definitions and structural lemmas for Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.BasicNotions.Examples₂
def prodPowSubOne (g : ℕ) : ℕ := ((List.range 9).map fun i => g ^ (i + 1) - 1).prod
end Formalism.BasicNotions.Examples₂


