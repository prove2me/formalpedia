-- Prove2me | Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing
-- name    : TheoryOfGames_SimpleGames_WinningLosing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:43:35.201157+00:00
-- url     : https://prove2.me/theorems/7ab16488-f10f-44e0-915b-a4547b8fc7c5
-- title:
--   Flat sets, winning and losing coalitions W_Γ, L_Γ, simple games, minimal winning coalitions W^m, and (49:W*)
-- statement:
--   Let $v$ be the characteristic function of a zero-sum $n$-person game $\Gamma$ with players $I = \{1, \dots, n\}$.
--
--   1. A set $S \subseteq I$ is **flat** (31.1.4, (31:3)) if $v(S) = \sum_{k \in S} v((k))$.
--   2. (49:L) $L_\Gamma$ is the set of all flat sets $S \subseteq I$ — the **losing** coalitions.
--   3. (49:W) $W_\Gamma$ is the set of all sets $S \subseteq I$ for which $-S$ is flat — the **winning** coalitions.
--   4. (49.4) An essential game which fulfils
--   $$\text{(49:1:b)}\qquad W_\Gamma \cup L_\Gamma = \bar I$$
--   ($\bar I$ the system of all subsets of $I$) is called **simple**.
--   5. (49.6.3) The **minimal** elements of a system $W$ are those $S$ of $W$ of which no proper subset belongs to $W$; for $W = W_\Gamma$ their set is $W^m_\Gamma$, the minimal winning coalitions.
--   6. (49:W*) A system $W \subseteq \bar I$ satisfies: (49:W*:a) of two complements $S, -S$ one and only one belongs to $W$; (49:W*:b) $W$ contains the supersets of its elements; (49:W*:c) $W$ contains $I$ and all $(n-1)$-element sets.
--
--   These are the basic objects of the theory of simple games: a game is simple when every coalition is either definitely winning or definitely losing, and (49:W*) is the book's characterization of the winning systems of simple games (49.6.2).
--
--   **Formalization Note** `losingSets v`, `winningSets v` and `minimalSets W` are of type `Set (Finset (Fin n))`. `IsSimple v` is `¬ IsInessential v` together with (49:1:b). `minimalSets` is defined for any system `W`, so that $W^m$ of the game and of a weighted majority can both be written with it. The $(n-1)$-element sets of (49:W*:c) are the `S` with `S.card + 1 = n`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 275, 31.1.4, (31:3); p. 423, (49:L); p. 424, (49:W), (49:1); p. 428, 49.4, (49:1:b); p. 429, (49:W*); p. 430, 49.6.3

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Solution

namespace TheoryOfGames.SimpleGames

/-- 31.1.4, (31:3): a set `S` of players is *flat* if `v(S) = ∑_{k in S} v((k))`. -/
def IsFlat {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : Prop :=
  v S = ∑ k ∈ S, v {k}

/-- (49:L), 49.1.2: `L_Γ` is the set of all flat sets `S (⊆ I)` — the losing coalitions. -/
def losingSets {n : ℕ} (v : Finset (Fin n) → ℝ) : Set (Finset (Fin n)) :=
  {S | IsFlat v S}

/-- (49:W), 49.1.2: `W_Γ` is the set of all sets `S (⊆ I)` for which `-S` is flat — the
winning coalitions. -/
def winningSets {n : ℕ} (v : Finset (Fin n) → ℝ) : Set (Finset (Fin n)) :=
  {S | IsFlat v Sᶜ}

/-- 49.4: an essential game which fulfills (49:1:b) `W_Γ ∪ L_Γ = Ī` (every subset of `I`
is winning or losing) is called *simple*. -/
def IsSimple {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ¬ IsInessential v ∧ ∀ S : Finset (Fin n), S ∈ winningSets v ∨ S ∈ losingSets v

/-- 49.6.3: the *minimal* elements of a system `W` of sets — those `S` of `W` of which no proper
subset belongs to `W`; for `W = W_Γ` their set is `W^m_Γ`, the minimal winning coalitions. -/
def minimalSets {n : ℕ} (W : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {S | S ∈ W ∧ ∀ T : Finset (Fin n), T ⊂ S → T ∉ W}

/-- (49:W*), 49.6.2: the properties characterizing the systems `W (⊆ Ī)` of winning
coalitions of simple games:
* (49:W*:a) of two complements (in `I`) `S`, `-S`, one and only one belongs to `W`;
* (49:W*:b) `W` contains the supersets of its elements;
* (49:W*:c) `W` contains `I` and all `(n - 1)`-element sets. -/
def SatisfiesWStar {n : ℕ} (W : Set (Finset (Fin n))) : Prop :=
  (∀ S : Finset (Fin n), (S ∈ W ↔ Sᶜ ∉ W)) ∧
  (∀ S T : Finset (Fin n), S ∈ W → S ⊆ T → T ∈ W) ∧
  (Finset.univ ∈ W ∧ ∀ S : Finset (Fin n), S.card + 1 = n → S ∈ W)

end TheoryOfGames.SimpleGames


