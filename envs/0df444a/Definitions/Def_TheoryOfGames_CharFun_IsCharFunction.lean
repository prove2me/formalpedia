-- Prove2me | Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
-- name    : TheoryOfGames_CharFun_IsCharFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T03:39:41.928983+00:00
-- url     : https://prove2.me/theorems/7064091c-f55f-411d-b16c-ceaed7eb1e42
-- title:
--   The conditions (25:3:a)–(25:3:c) on a set function
-- statement:
--   Let $I = \{1, \dots, n\}$ and let $v$ be a numerical set function, defined for all subsets $S$ of $I$. Write $-S = I \setminus S$ and $\ominus$ for the empty set. The function $v$ satisfies the conditions of 25.3.1 if
--
--   1. (25:3:a) $v(\ominus) = 0$;
--   2. (25:3:b) $v(-S) = -v(S)$ for every $S \subseteq I$;
--   3. (25:3:c) $v(S \cup T) \geqq v(S) + v(T)$ whenever $S \cap T = \ominus$.
--
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \ominus.$$
--
--   From 26.2 on the book calls every function satisfying these conditions a *characteristic function*, even when it is viewed without reference to any game; the §27 results are stated for such functions.
--
--   **Formalization Note** Coalitions are `Finset (Fin n)` and $-S$ is the complement `Sᶜ`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 241, 25.3.1, (25:3:a)–(25:3:c); p. 245, 26.2

import Mathlib

namespace TheoryOfGames.CharFun

/-- The conditions (25:3:a)–(25:3:c) of 25.3.1 on a numerical set function `v` defined for all
subsets `S` of `I = Fin n` (`-S` is the complement `Sᶜ`):
* (25:3:a) `v(∅) = 0`;
* (25:3:b) `v(-S) = -v(S)`;
* (25:3:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 26.2 on the book calls every function satisfying them a *characteristic function*. -/
def IsCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin n), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

end TheoryOfGames.CharFun


