-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInduction
-- name    : GroundTheory_LocalFields_BrauerInduction
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:14.479748+00:00
-- url     : https://prove2.me/theorems/3c5d6b76-0627-4e92-944e-4b534d464c7d
-- title:
--   Brauer Induction
-- statement:
--   Definitions and structural lemmas for Brauer Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInduction.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
end GroundTheory.LocalField


