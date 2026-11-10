-- Prove2me | Definitions.Def_NashOrTriangle_IsBinary
-- name    : NashOrTriangle_IsBinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:27.535686+00:00
-- url     : https://prove2.me/theorems/93f41478-b6f9-4048-8b1c-189b3ad17263
-- title:
--   Binary game: payoffs in $\{0,1\}$
-- statement:
--   A game is **binary** if its payoff takes only the values $0$ and $1$:
--   $$
--   M(a, b) \in \{0, 1\} \qquad \text{for all } a, b .
--   $$
--   A game that is not binary is called **real-valued**. Theorem 2.1 gives different bounds for the two cases.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- The game is **binary**: `M` takes only the values `0` and `1`. A game that is not binary is
called real-valued.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4): "The game is binary if M takes only the values 0 and 1,
and real-valued otherwise." -/
def IsBinary {A B : Type*} (M : A → B → ℚ) : Prop :=
  ∀ a b, M a b = 0 ∨ M a b = 1

end NashOrTriangle


