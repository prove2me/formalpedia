-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:27.196343+00:00
-- url     : https://prove2.me/theorems/a0140272-6290-43d2-a9b0-4ecf897ed2b3
-- title:
--   Restriction Of Blocks And Jordan
-- statement:
--   Definitions and structural lemmas for Restriction Of Blocks And Jordan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/RestrictionOfBlocksAndJordan.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
namespace Formalism.CyclotomicNorms
section SlopeTestRemainingChoices
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
end SlopeTestRemainingChoices
end Formalism.CyclotomicNorms


