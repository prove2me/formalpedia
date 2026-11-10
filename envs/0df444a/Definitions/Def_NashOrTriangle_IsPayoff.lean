-- Prove2me | Definitions.Def_NashOrTriangle_IsPayoff
-- name    : NashOrTriangle_IsPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:25.445267+00:00
-- url     : https://prove2.me/theorems/a0323464-43d9-4d07-8526-ec7db562da52
-- title:
--   Payoff function of a game: values in $[0,1]\cap\mathbb Q$
-- statement:
--   A two-player zero-sum game $G = (A, B, M)$ has strategy sets $A$ (rows, the maximizing player) and $B$ (columns, the minimizing player) and a payoff $M : A \times B \to [0,1] \cap \mathbb Q$ to the row player. This predicate says that $M$ is such a payoff function:
--   $$
--   0 \le M(a, b) \le 1 \qquad \text{for all } a \in A,\ b \in B .
--   $$
--   It is the standing assumption on every game of the mission.
--
--   **Formalization Note** Strategy sets are types. The paper's games have nonempty countable strategy sets; these are hypotheses (`Countable`, `Nonempty`, or `Fintype` for finite games) of the theorems, not part of the predicate.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- `M : A → B → ℚ` is the payoff function of a game in the sense of the paper: every payoff to
the row player lies in `[0, 1] ∩ ℚ`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4): "M : A × B → [0, 1] ∩ Q is the payoff to the row player".

**Formalization Note** Strategy sets are types; countability and nonemptiness of `A` and `B`
are hypotheses of the theorems that use a game, not part of this predicate. -/
def IsPayoff {A B : Type*} (M : A → B → ℚ) : Prop :=
  ∀ a b, 0 ≤ M a b ∧ M a b ≤ 1

end NashOrTriangle


