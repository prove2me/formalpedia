-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:44.485037+00:00
-- url     : https://prove2.me/theorems/1cf63e4a-e0d0-421d-a714-e0cf7911ab51
-- title:
--   Flat Quotient Of Equiv Coker Dual Map Of Exact Fibres
-- statement:
--   Definitions and structural lemmas for Flat Quotient Of Equiv Coker Dual Map Of Exact Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
namespace GlobalTheory
namespace DualCokernelFlat
section Modules
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
end Modules
end DualCokernelFlat
end GlobalTheory


