-- Prove2me | Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
-- name    : TheoryOfGames_Decomposition_IsConstantSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:08:41.394739+00:00
-- url     : https://prove2.me/theorems/a450427b-faaa-43f7-99ae-2a7328396101
-- title:
--   Characteristic functions of constant-sum games (42:6:a)–(42:6:c), (42:D); inessentiality (42:F)
-- statement:
--   Let $I$ be a finite set of players and let $v$ assign a real number $v(S)$ to every subset $S \subseteq I$ (every *coalition*, including the empty set $\ominus$ and $I$ itself). Write $-S = I - S$ for the complement of $S$ in $I$.
--
--   **Constant-sum characteristic function.** $v$ satisfies the conditions (42:6:a)–(42:6:c) if
--
--   1. (42:6:a) $v(\ominus) = 0$;
--   2. (42:6:b) $v(S) + v(-S) = v(I)$ for every $S \subseteq I$;
--   3. (42:6:c) $v(S) + v(T) \leqq v(S \cup T)$ whenever $S \cap T = \ominus$.
--
--   By (42:D) these are exactly the characteristic functions of constant-sum games; from 42.4.1 on the book considers characteristic functions $v(S)$ subject to (42:6:a)–(42:6:c) only, with $v(I)$ arbitrary.
--
--   **Inessentiality.** Two such functions are *strategically equivalent* when one arises from the other by the transformation (42:5),
--   $$v'(S) \equiv v(S) + \sum_{k \in S} \alpha^0_k,$$
--   with arbitrary real $\alpha^0_k$ (no longer subject to $\sum_k \alpha^0_k = 0$). By (42:F) a constant-sum game is *inessential* if it is strategically equivalent to the game with $\bar v(S) \equiv 0$, i.e. if there are real numbers $\alpha^0_k$, $k \in I$, with
--   $$v(S) + \sum_{k \in S} \alpha^0_k = 0 \quad \text{for all } S \subseteq I.$$
--
--   These are the standing domain of the whole of §43 and the notion of inessentiality used in (43:J).
--
--   **Formalization Note** The set of players is an arbitrary finite type `ι` (the book's $I = (1, \dots, n)$; in Chapter IX players are also named $1', \dots, k', 1'', \dots, l''$), coalitions are `Finset ι`, and $-S$ is the complement `Sᶜ`, taken in $I$. `IsConstantSum` is a structure with the three conditions as fields; `IsInessential` is in the same file.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 349, 42.3.2, (42:6:a)–(42:6:c), (42:D); p. 348, (42:5); p. 350, 42.4.1; p. 351, (42:F)

import Mathlib

namespace TheoryOfGames.Decomposition

/-- The conditions (42:6:a)–(42:6:c) of 42.3.2 on a numerical set function `v`, defined for all
subsets `S` of the (finite) set of players `I = ι` (`-S` is the complement `Sᶜ`, `⊖` is `∅`):
* (42:6:a) `v(⊖) = 0`;
* (42:6:b) `v(S) + v(-S) = v(I)`;
* (42:6:c) `v(S) + v(T) ≤ v(S ∪ T)` if `S ∩ T = ⊖`.
By (42:D) these are exactly the characteristic functions of constant-sum games. -/
structure IsConstantSum {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Finset ι → ℝ) : Prop where
  /-- (42:6:a) -/
  empty : v ∅ = 0
  /-- (42:6:b) -/
  compl : ∀ S : Finset ι, v S + v Sᶜ = v Finset.univ
  /-- (42:6:c) -/
  superadd : ∀ S T : Finset ι, Disjoint S T → v S + v T ≤ v (S ∪ T)

/-- Inessentiality of a constant-sum game (42:F), 42.5.1: `v` is strategically equivalent, in the
sense of (42:5) (`v'(S) = v(S) + ∑_{k ∈ S} α⁰_k` with arbitrary real `α⁰_1, …, α⁰_n`), to the
game with `v̄(S) ≡ 0`. -/
def IsInessential {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Finset ι → ℝ) : Prop :=
  ∃ α₀ : ι → ℝ, ∀ S : Finset ι, v S + ∑ k ∈ S, α₀ k = 0

end TheoryOfGames.Decomposition


