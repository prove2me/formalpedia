-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:13.327593+00:00
-- url     : https://prove2.me/theorems/d335eeee-000e-4872-b4bc-14a137043639
-- title:
--   Unram Sub
-- statement:
--   Definitions and structural lemmas for Unram Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
def UnramSub {V F : Type} [CommRing V] [Field F] (i : V →+* F) (T : Subring F) : Prop :=
  ∃ (_ : IsDiscreteValuationRing T) (f : V →+* T), (∀ v, (f v : F) = i v) ∧ ∀ π : V, Irreducible π → Irreducible (f π)
namespace UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}
end UnramSub
end GlobalTheory


