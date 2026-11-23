-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:35.602836+00:00
-- url     : https://prove2.me/theorems/c520e390-a55b-4d52-a5aa-4ee1af46a284
-- title:
--   Double Coset Operators Comm Of Anti Involution
-- statement:
--   Definitions and structural lemmas for Double Coset Operators Comm Of Anti Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetOperatorsCommOfAntiInvolution.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
namespace GlobalTheory
namespace GelfandTrick
variable {G : Type} [Group G]
def InDoubleCoset (J : Subgroup G) (a y : G) : Prop := ∃ k₁ ∈ J, ∃ k₂ ∈ J, y = k₁ * a * k₂
end GelfandTrick
end GlobalTheory


