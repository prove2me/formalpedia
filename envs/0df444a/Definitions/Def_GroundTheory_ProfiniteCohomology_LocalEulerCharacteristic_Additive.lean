-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:01.60561+00:00
-- url     : https://prove2.me/theorems/5d224720-6dbb-4216-a2b3-1d7437f8812a
-- title:
--   Additive
-- statement:
--   Definitions and structural lemmas for Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/Additive.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
universe u v
open Representation
namespace AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
end AdditiveFunction
end GroundTheory.ProfCoh


