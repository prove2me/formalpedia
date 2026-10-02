-- Prove2me | Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions
-- name    : TheoryOfGames_GeneralGames_CharFunConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:15:31.683389+00:00
-- url     : https://prove2.me/theorems/8321e26d-f9e7-4be1-bee7-e6fbad772956
-- title:
--   The conditions (57:1:a)–(57:1:c) and (57:2:a), (57:2:c) on a set function
-- statement:
--   Let $I = \{1, \dots, n\}$ and $\overline I = \{1, \dots, n, n+1\}$.
--
--   A numerical set function $v(S)$, $S \subseteq \overline I$, satisfies **(57:1:a)–(57:1:c)** if, writing $\bot S = \overline I - S$,
--   $$\text{(57:1:a)}\ v(\emptyset) = 0, \qquad \text{(57:1:b)}\ v(\bot S) = -v(S), \qquad \text{(57:1:c)}\ v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset .$$
--
--   A numerical set function $v(S)$, $S \subseteq I$, satisfies **(57:2:a), (57:2:c)** if
--   $$\text{(57:2:a)}\ v(\emptyset) = 0, \qquad \text{(57:2:c)}\ v(S \cup T) \geqq v(S) + v(T) \ \text{ if } S \cap T = \emptyset .$$
--
--   After 57.3.4 the book calls such functions *extended* and *restricted characteristic functions* respectively, even without reference to any game.
--
--   **Formalization Note** $I$ is `Fin n`, $\overline I$ is `Fin (n + 1)`, sets are `Finset`s and $\bot S$ is the complement `Sᶜ` in `Fin (n + 1)`. The conditions are the predicates `IsExtendedCharFunction` and `IsRestrictedCharFunction`; no condition on $v(I)$ is imposed.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 528–529, 57.2.1, (57:1:a)–(57:1:c), (57:2:a), (57:2:c); p. 533, end of 57.3.4

import Mathlib

namespace TheoryOfGames.GeneralGames

/-- The conditions (57:1:a)–(57:1:c) of 57.2.1 on a numerical set function `v` on all subsets
`S` of `Ī = (1, …, n, n + 1) = Fin (n + 1)` (`⊥S` is the complement `Ī - S = Sᶜ`):
* (57:1:a) `v(∅) = 0`;
* (57:1:b) `v(⊥S) = -v(S)`;
* (57:1:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 57.3.4 on the book calls such functions *extended characteristic functions*. -/
def IsExtendedCharFunction {n : ℕ} (v : Finset (Fin (n + 1)) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin (n + 1)), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin (n + 1)), Disjoint S T → v S + v T ≤ v (S ∪ T))

/-- The conditions (57:2:a), (57:2:c) of 57.2.1 on a numerical set function `v` on all subsets
`S` of `I = (1, …, n) = Fin n`:
* (57:2:a) `v(∅) = 0`;
* (57:2:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
From 57.3.4 on the book calls such functions *restricted characteristic functions*. -/
def IsRestrictedCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

end TheoryOfGames.GeneralGames


