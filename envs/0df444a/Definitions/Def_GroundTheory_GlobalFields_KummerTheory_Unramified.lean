-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Unramified
-- name    : GroundTheory_GlobalFields_KummerTheory_Unramified
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:48.16806+00:00
-- url     : https://prove2.me/theorems/c572a1b7-aafb-4486-b51f-df51bc0a62cb
-- title:
--   Unramified
-- statement:
--   Definitions and structural lemmas for Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Unramified.lean

import Mathlib
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
open NumberField IsDedekindDomain Polynomial
namespace Kummer
variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [Field M] [NumberField M] [Algebra K M]
end Kummer
end GroundTheory.Global


