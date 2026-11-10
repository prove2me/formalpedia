-- Prove2me | Definitions.Def_NashOrTriangle_HasMarginTriangle
-- name    : NashOrTriangle_HasMarginTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:21.067205+00:00
-- url     : https://prove2.me/theorems/5a953cf4-57aa-40a5-a2df-0ecfd10b8bb4
-- title:
--   The game contains a $(t,\gamma)$-triangle
-- statement:
--   The game $M$ **contains a $(t, \gamma)$-triangle** if there are rows $a_1, \dots, a_t$ and columns $b_1, \dots, b_t$ forming a $(t, \gamma)$-triangle.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4), display (1)

import Mathlib
import Definitions.Def_NashOrTriangle_IsMarginTriangle

namespace NashOrTriangle

/-- The game `M` contains a `(t, γ)`-triangle.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4), display (1). -/
def HasMarginTriangle {A B : Type*} (M : A → B → ℚ) (t : ℕ) (γ : ℝ) : Prop :=
  ∃ a : Fin t → A, ∃ b : Fin t → B, IsMarginTriangle M γ a b

end NashOrTriangle


