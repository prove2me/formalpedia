-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:10.375674+00:00
-- url     : https://prove2.me/theorems/e1b54ea5-9a2f-46f8-a677-fc947cb8bc41
-- title:
--   Aut CFixed
-- statement:
--   Definitions and structural lemmas for Aut CFixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AutCFixed.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
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
open Polynomial IntermediateField
section General
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
variable [CharZero Ω]
end General
end GroundTheory.Global


