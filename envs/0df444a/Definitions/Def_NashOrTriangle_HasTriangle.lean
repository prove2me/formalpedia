-- Prove2me | Definitions.Def_NashOrTriangle_HasTriangle
-- name    : NashOrTriangle_HasTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:23.556684+00:00
-- url     : https://prove2.me/theorems/1107bf61-d622-437a-80d9-31cfb5c6379a
-- title:
--   The game contains a $t$-triangle
-- statement:
--   The game $M$ **contains a $t$-triangle** if there are rows $a_1, \dots, a_t$ and columns $b_1, \dots, b_t$ forming a $t$-triangle.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_IsTriangle

namespace NashOrTriangle

/-- The game `M` contains a `t`-triangle.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4). -/
def HasTriangle {A B : Type*} (M : A → B → ℚ) (t : ℕ) : Prop :=
  ∃ a : Fin t → A, ∃ b : Fin t → B, IsTriangle M a b

end NashOrTriangle


