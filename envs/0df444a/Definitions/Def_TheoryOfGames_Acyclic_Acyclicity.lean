-- Prove2me | Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
-- name    : TheoryOfGames_Acyclic_Acyclicity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:43:46.775892+00:00
-- url     : https://prove2.me/theorems/981f9911-3b7c-46f6-a6d7-754ceb3b1c9f
-- title:
--   Acyclicity (65:D:c), strict acyclicity (A_∞) and the maxima property (65:K)
-- statement:
--   Let $D$ be a set and $\mathcal S$ a relation on $D$ ($x\mathcal S y$: "$x$ dominates $y$").
--
--   1. **Condition $(A_m)$** (65:D), for $m = 1, 2, \dots$: never $x_1\mathcal S x_0,\ x_2\mathcal S x_1,\ \dots,\ x_m\mathcal S x_{m-1}$, where $x_0 = x_m$ and $x_0, x_1, \dots, x_{m-1}$ belong to $D$.
--   2. **Acyclicity** (65:D:c): $\mathcal S$ is acyclic if it fulfills all conditions $(A_1), (A_2), (A_3), \dots$. In particular $(A_1)$ says that never $x\mathcal S x$.
--   3. **Condition $(A_\infty)$ and strict acyclicity** (65.6.2): never $x_1\mathcal S x_0,\ x_2\mathcal S x_1,\ x_3\mathcal S x_2, \dots$, where $x_0, x_1, x_2, \dots$ belong to $D$ (the indices go on ad infinitum; the $x_i$ need not all be different). $\mathcal S$ is strictly acyclic if it fulfills $(A_\infty)$.
--   4. **Property (65:K)**: for every $E \subseteq D$,
--   $$E \neq \ominus \implies E^m \neq \ominus,$$
--   i.e. every non-empty subset of $D$ possesses maxima ($\ominus$ is the empty set and $E^m$ the set of maxima of $E$).
--
--   These are the conditions under which §65 proves existence and uniqueness of solutions; the book shows that strict acyclicity is exactly (65:K) and that for finite $D$ acyclicity and strict acyclicity coincide.
--
--   **Formalization Note** A finite or infinite sequence is a function `x : ℕ → α`. `CycleCondition D S m` quantifies over all `x` with $x_0, \dots, x_{m-1} \in D$ and $x_m = x_0$ and asserts that not all of $S\,x_{i+1}\,x_i$ ($i < m$) hold. `IsAcyclic D S` requires this for every $m \ge 1$ (the case $m = 0$ is excluded, as in the book). `IsStrictlyAcyclic D S` says that no sequence in $D$ has $S\,x_{i+1}\,x_i$ for all $i$. `HasMaximaProperty D S` is (65:K), quantified over all subsets $E \subseteq D$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 590–591, (65:D), (65:D:c); p. 595, 65.6.1, (65:K); 65.6.2, (A_∞)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution

namespace TheoryOfGames.Acyclic

/-- (65:D), condition `(A_m)`: never `x₁ S x₀, x₂ S x₁, …, x_m S x_{m−1}`, where `x₀ = x_m` and
`x₀, x₁, …, x_{m−1}` belong to `D`. A finite sequence is given as `x : ℕ → α`, of which only
`x 0, …, x m` matter. -/
def CycleCondition {α : Type*} (D : Set α) (S : α → α → Prop) (m : ℕ) : Prop :=
  ∀ x : ℕ → α, (∀ i < m, x i ∈ D) → x m = x 0 → ¬ ∀ i < m, S (x (i + 1)) (x i)

/-- (65:D:c): a relation `S` is *acyclic* (on `D`) if it fulfills all conditions
`(A_1), (A_2), (A_3), …`. -/
def IsAcyclic {α : Type*} (D : Set α) (S : α → α → Prop) : Prop :=
  ∀ m : ℕ, 1 ≤ m → CycleCondition D S m

/-- 65.6.2, condition `(A_∞)`: never `x₁ S x₀, x₂ S x₁, x₃ S x₂, …`, where `x₀, x₁, x₂, …`
belong to `D` (the indices go on ad infinitum; the `xᵢ` need not be distinct). `S` is
*strictly acyclic* (on `D`) if it fulfills `(A_∞)`. -/
def IsStrictlyAcyclic {α : Type*} (D : Set α) (S : α → α → Prop) : Prop :=
  ¬ ∃ x : ℕ → α, (∀ i, x i ∈ D) ∧ ∀ i, S (x (i + 1)) (x i)

/-- (65:K): `E ≠ ⊖` (for `E ⊆ D`) implies `E^m ≠ ⊖`, i.e. every non-empty subset of `D`
possesses maxima. -/
def HasMaximaProperty {α : Type*} (D : Set α) (S : α → α → Prop) : Prop :=
  ∀ E : Set α, E ⊆ D → E.Nonempty → (maxima E S).Nonempty

end TheoryOfGames.Acyclic


