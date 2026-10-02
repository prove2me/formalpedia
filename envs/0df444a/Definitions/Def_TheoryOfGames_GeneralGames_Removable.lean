-- Prove2me | Definitions.Def_TheoryOfGames_GeneralGames_Removable
-- name    : TheoryOfGames_GeneralGames_Removable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:16:58.857591+00:00
-- url     : https://prove2.me/theorems/ba6a228b-7237-4d7b-b1ce-7955ab9e0ccd
-- title:
--   Removable sets of players (57:A) and inessentiality (57:13)
-- statement:
--   Let $\Gamma$ be a zero-sum $n$-person game with payoffs $\mathcal H_k(\tau_1, \dots, \tau_n)$ and characteristic function $v(S)$, $S \subseteq I = \{1,\dots,n\}$.
--
--   1. A player $j$ has **no influence upon the course of the game** if every $\mathcal H_k(\tau_1, \dots, \tau_n)$ is independent of the variable $\tau_j$.
--   2. **(57:A)** A set $S \subseteq I$ is **removable** for $\Gamma$ if there is another zero-sum $n$-person game $\Gamma'$ which has the same characteristic function as $\Gamma$ but in which no player belonging to $S$ has an influence upon the course of the game.
--   3. A characteristic function is **inessential** if it has the form (57:13)
--   $$v(S) = \sum_{k \in S} \alpha_k \qquad \text{for all } S \subseteq I$$
--   for suitable constants $\alpha_1, \dots, \alpha_n$ (the book remarks on p. 534 that (57:13) "is precisely the definition of inessentiality"; cf. (27:C)).
--
--   Removability measures how far the strategic role of a group of players can be reproduced by a game in which they make no moves at all.
--
--   **Formalization Note** "No influence" is read as independence of all payoffs from $\tau_j$, which is how the proof of (57:C) on p. 534 uses it. $\Gamma'$ may have strategy sets different from those of $\Gamma$. The characteristic function of a zero-sum game is `restrictedCharFun` (57.1).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 533, 57.4.1, (57:A); p. 534, 57.4.2, (57:12), (57:13); p. 251, (27:C)

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun

namespace TheoryOfGames.GeneralGames

namespace GeneralGame

variable {n : ℕ}

/-- Player `j` has *no influence upon the course of the game* `Γ` if all the functions
`ℋ_k(τ₁, …, τₙ)` are independent of the variable `τ_j` (the reading used in the proof of (57:C),
p. 534, and in 56.2.2 for the fictitious player). -/
def NoInfluence (Γ : GeneralGame n) (j : Fin n) : Prop :=
  ∀ τ τ' : (k : Fin n) → Fin (Γ.β k), (∀ i, i ≠ j → τ i = τ' i) → Γ.H τ = Γ.H τ'

/-- (57:A): for a zero-sum `n`-person game `Γ` and a set `S ⊆ I`, `S` is *removable* for `Γ`
if there is another zero-sum `n`-person game `Γ'` which has the same characteristic function as
`Γ` but in which no player belonging to `S` has an influence upon the course of the game.
(For zero-sum games the characteristic function of 25.1.3 is `restrictedCharFun`, 57.1.) -/
def IsRemovable (Γ : GeneralGame n) (S : Finset (Fin n)) : Prop :=
  ∃ Γ' : GeneralGame n, Γ'.IsZeroSum ∧ Γ'.restrictedCharFun = Γ.restrictedCharFun ∧
    ∀ j ∈ S, Γ'.NoInfluence j

end GeneralGame

/-- Inessentiality of a characteristic function, in the form (57:13) (= (27:C)):
`v(S) = ∑_{k ∈ S} α_k` for all `S ⊆ I`, for a suitable system of constants `α₁, …, αₙ`
("(57:13) is precisely the definition of inessentiality", p. 534). -/
def IsInessential {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∃ α : Fin n → ℝ, ∀ S : Finset (Fin n), v S = ∑ k ∈ S, α k

end TheoryOfGames.GeneralGames


