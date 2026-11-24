-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:20.9598+00:00
-- url     : https://prove2.me/theorems/44f3cbff-0358-4fef-9508-222b3ccc1bb9
-- title:
--   Padic Val Int Prod Eleven Multiples
-- statement:
--   Definitions and structural lemmas for Padic Val Int Prod Eleven Multiples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/PadicValIntProdElevenMultiples.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
def elevenMultiples : Finset ℤ := {11, -11, 22, -22, 33, -33, 44, -44, 55, -55, 66, -66, 77, -77}
end Formalism.CohomologicalDescent


