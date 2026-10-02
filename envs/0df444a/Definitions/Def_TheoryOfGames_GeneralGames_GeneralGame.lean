-- Prove2me | Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
-- name    : TheoryOfGames_GeneralGames_GeneralGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:11:52.66628+00:00
-- url     : https://prove2.me/theorems/d0b2f6ff-460e-492e-bbb8-450ddd77a764
-- title:
--   General n-person game in normalized form (11.2.3, 56.2.2)
-- statement:
--   A **general $n$-person game in normalized form** $\Gamma$ (11.2.3, 56.2.2) consists of the following data.
--
--   1. Players $k = 1, \dots, n$. Each player $k$ chooses a variable $\tau_k = 1, \dots, \beta_k$, where $\beta_k \geqq 1$ is the number of his pure strategies; each player is uninformed about the other players' choices.
--   2. For every choice $(\tau_1, \dots, \tau_n)$, player $k$ gets the real amount $\mathcal H_k(\tau_1, \dots, \tau_n)$.
--
--   No condition is imposed on the sum $\sum_{k=1}^n \mathcal H_k$: this is what makes the game *general* rather than zero-sum. The game is called **zero-sum** if, as in (25:1),
--   $$\sum_{k=1}^{n} \mathcal H_k(\tau_1, \dots, \tau_n) \equiv 0 .$$
--
--   General games are the objects of Chapter XI; the zero-sum games of Chapter VI are the special case satisfying (25:1).
--
--   **Formalization Note** Players are indexed by `Fin n`, i.e. $0, \dots, n-1$ instead of $1, \dots, n$, and the strategies of player $k$ by `Fin (β k)`. The condition $\beta_k \geqq 1$ is a field of the structure. The zero-sum property is the separate predicate `GeneralGame.IsZeroSum`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 506, 56.2.2; 11.2.3; p. 239, (25:1)

import Mathlib

namespace TheoryOfGames.GeneralGames

/-- A general `n`-person game in normalized form (11.2.3, 56.2.2): no zero-sum condition.
Players are `k : Fin n` (the book's players `1, …, n` are `0, …, n - 1` here). Player `k`
chooses `τ k : Fin (β k)`, one of `β k ≥ 1` pure strategies (the book's `τ_k = 1, …, β_k`),
each player uninformed about the others' choices. When the profile `τ = (τ₁, …, τₙ)` is
played, player `k` receives `H τ k` (the book's `ℋ_k(τ₁, …, τₙ)`), an arbitrary real number. -/
structure GeneralGame (n : ℕ) where
  /-- `β k` is the number of pure strategies of player `k`. -/
  β : Fin n → ℕ
  /-- Every player has at least one pure strategy. -/
  β_pos : ∀ k, 0 < β k
  /-- `H τ k = ℋ_k(τ₁, …, τₙ)`, the amount player `k` gets. -/
  H : ((k : Fin n) → Fin (β k)) → Fin n → ℝ

/-- A general game is *zero-sum* (25:1) if `∑_{k=1}^n ℋ_k(τ₁, …, τₙ) ≡ 0`: the zero-sum
`n`-person games of Chapter VI are exactly the general games with this property. -/
def GeneralGame.IsZeroSum {n : ℕ} (Γ : GeneralGame n) : Prop :=
  ∀ τ, ∑ k, Γ.H τ k = 0

end TheoryOfGames.GeneralGames


