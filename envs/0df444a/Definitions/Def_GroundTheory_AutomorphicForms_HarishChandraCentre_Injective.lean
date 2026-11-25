-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:25.388186+00:00
-- url     : https://prove2.me/theorems/5f03789c-e6b1-5954-b05c-8e9038ffcef1
-- title:
--   Injective
-- statement:
--   Definitions and structural lemmas for Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
end GroundTheory.Automorphic.HarishChandra


