-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:43.917276+00:00
-- url     : https://prove2.me/theorems/9a2efada-37f2-43ee-8007-3e6bb4d910c5
-- title:
--   Cond Sq
-- statement:
--   Definitions and structural lemmas for Cond Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondSq.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace UpperTheory.Ram
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
end UpperTheory.Ram


