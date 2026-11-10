-- Prove2me | Definitions.Def_NashOrTriangle_complement
-- name    : NashOrTriangle_complement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:35.710006+00:00
-- url     : https://prove2.me/theorems/c8c549a7-98fd-425f-b0b6-926303b1919c
-- title:
--   Complemented game $1-H$
-- statement:
--   The **complemented game** $1 - H$ of a game $H$ with payoff $M$ has payoff
--   $$
--   (1 - M)(a, b) = 1 - M(a, b).
--   $$
--   It enters the triangle dimension $d_H$ of Appendix C.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, p.23 (PDF p.24)

import Mathlib

namespace NashOrTriangle

/-- The complemented game `1 − H`: payoff `1 − M(a, b)`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, printed p. 23 (PDF p. 24): "in H or in the complemented game 1 − H". -/
def complement {A B : Type*} (M : A → B → ℚ) : A → B → ℚ :=
  fun a b => 1 - M a b

end NashOrTriangle


