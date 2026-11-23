-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:56.519118+00:00
-- url     : https://prove2.me/theorems/bccebf48-1b52-44a1-93c5-93b7e53dac48
-- title:
--   Exists Ring Equiv Extend Of Is Transcendence Basis
-- statement:
--   Definitions and structural lemmas for Exists Ring Equiv Extend Of Is Transcendence Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ExistsRingEquivExtendOfIsTranscendenceBasis.lean

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
open Cardinal Polynomial IntermediateField
section General
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
end General
end GroundTheory.Global


