-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:28.487802+00:00
-- url     : https://prove2.me/theorems/2e532ab0-cf23-43cf-8664-ca4afd7e2487
-- title:
--   Fun Kit
-- statement:
--   Definitions and structural lemmas for Fun Kit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FunKit.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
namespace UpperTheory.Ram.Fun
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
end UpperTheory.Ram.Fun
end


