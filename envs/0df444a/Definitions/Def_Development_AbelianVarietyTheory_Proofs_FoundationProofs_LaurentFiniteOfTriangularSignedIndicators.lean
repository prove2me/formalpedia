-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:06.626812+00:00
-- url     : https://prove2.me/theorems/6acac45a-272e-4339-b2a0-25b2c120b98e
-- title:
--   Laurent Finite Of Triangular Signed Indicators
-- statement:
--   Definitions and structural lemmas for Laurent Finite Of Triangular Signed Indicators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LaurentFinite
open AddMonoidAlgebra
def cut (j n : ℤ) : ℤ := if j ≤ |n| then Int.sign n else 0
end GlobalTheory.LaurentFinite


