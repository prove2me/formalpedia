-- Prove2me | Definitions.Def_MondererShapley_Congestion_IsIsomorphic
-- name    : MondererShapley_Congestion_IsIsomorphic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:40.960306+00:00
-- url     : https://prove2.me/theorems/a08ec8eb-3eb0-4a90-8263-bfce4e664c87
-- title:
--   Isomorphic games in strategic form (Monderer–Shapley, p. 133)
-- statement:
--   Let $\Gamma_1$ and $\Gamma_2$ be games in strategic form with the same set of players $N$. For $k = 1, 2$ let $(Y^i_k)_{i \in N}$ be the strategy sets of $\Gamma_k$ and $(u^i_k)_{i\in N}$ its payoff functions. The games $\Gamma_1$ and $\Gamma_2$ are **isomorphic** if there exist bijections $g^i : Y^i_1 \to Y^i_2$, $i \in N$, such that for every player $i \in N$
--
--   $$u^i_1(y^1, y^2, \dots, y^n) = u^i_2\big(g^1(y^1), g^2(y^2), \dots, g^n(y^n)\big) \qquad \text{for every } (y^1, \dots, y^n) \in Y_1 = \times_{i\in N} Y^i_1.$$
--
--   Isomorphic games differ only in the names of the strategies; every strategic property (equilibria, potentials, improvement paths) transfers along the bijections.
--
--   **Formalization Note.** The bijections are Lean equivalences `Y₁ i ≃ Y₂ i`, one per player; the strategy types of the two games may live in different universes.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 133 (PDF p. 10), definition of isomorphic games

import Mathlib

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 133: two games in strategic form with the same set of players `ι`,
strategy sets `Y₁ i`, `Y₂ i` and payoffs `u₁ i`, `u₂ i`, are isomorphic if there exist bijections
`gⁱ : Yⁱ₁ → Yⁱ₂` such that `uⁱ₁(y¹, …, yⁿ) = uⁱ₂(g¹(y¹), …, gⁿ(yⁿ))` for every player `i` and every
profile `(y¹, …, yⁿ) ∈ Y₁`. -/
def IsIsomorphic {ι : Type*} {Y₁ : ι → Type*} {Y₂ : ι → Type*}
    (u₁ : ι → (∀ i, Y₁ i) → ℝ) (u₂ : ι → (∀ i, Y₂ i) → ℝ) : Prop :=
  ∃ g : ∀ i, Y₁ i ≃ Y₂ i, ∀ (i : ι) (y : ∀ i, Y₁ i), u₁ i y = u₂ i (fun j => g j (y j))

end MondererShapley.Congestion


