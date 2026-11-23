-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
-- name    : GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:33.384905+00:00
-- url     : https://prove2.me/theorems/d15a0902-ab42-42cf-b450-752c79e0160a
-- title:
--   Arch Chars Units
-- statement:
--   Definitions and structural lemmas for Arch Chars Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open Complex
noncomputable def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_subtype_val.congr fun _ => rfl)
end GroundTheory.Global


