-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:56.859116+00:00
-- url     : https://prove2.me/theorems/6fb8ef91-10ed-4c0d-ae8b-d060aba8599a
-- title:
--   First Order Rigid
-- statement:
--   Definitions and structural lemmas for First Order Rigid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.TangentRigid
def Top {k : Type} [Field k] (p : k[X]) (d : ℕ) (c : k) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = c
section
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}
end
end GlobalTheory.TangentRigid


