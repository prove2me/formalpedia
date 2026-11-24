-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:33:12.492917+00:00
-- url     : https://prove2.me/theorems/fcfa0492-0b18-4020-a6c3-d1e582014cf2
-- title:
--   Span Equality
-- statement:
--   Definitions and structural lemmas for Span Equality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SpanEquality.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertSpan
section Vec
variable {L : Type} [Field L] {N : ℕ}
def vec3 (x : L) (w : Fin N → L) (t : L) : Fin (N + 2) → L :=
  Fin.cons (α := fun _ => L) x (Fin.snoc (α := fun _ => L) w t)
def mat3 (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  Matrix.of (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l))
end Vec
section Lat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
end Lat
section Main
variable {L : Type} [Field L] {N : ℕ}
end Main
end GlobalTheory.CompanionTheory.InertSpan
end


