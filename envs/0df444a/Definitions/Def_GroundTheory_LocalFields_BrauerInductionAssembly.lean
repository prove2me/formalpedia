-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
-- name    : GroundTheory_LocalFields_BrauerInductionAssembly
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:12:49.894867+00:00
-- url     : https://prove2.me/theorems/bb71cef5-21d8-4560-874b-0b677bd934dc
-- title:
--   Brauer Induction Assembly
-- statement:
--   Definitions and structural lemmas for Brauer Induction Assembly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionAssembly.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
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
variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono
end GroundTheory.LocalField


