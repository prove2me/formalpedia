-- Prove2me | Definitions.Def_TheoryOfGames_SimpleGames_Solution
-- name    : TheoryOfGames_SimpleGames_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:41:33.46112+00:00
-- url     : https://prove2.me/theorems/179497bb-2dd3-4eb2-a3b7-6e393bc95740
-- title:
--   Characteristic functions, imputations, domination, solutions (30.1.1) and inessential games (27.3)
-- statement:
--   Let $I = \{1, \dots, n\}$ be the set of players of a zero-sum $n$-person game and let $v(S)$ be a numerical function defined for all subsets $S \subseteq I$. The standing properties of a **characteristic function** (25.3.1) are
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \text{ if } S \cap T = \ominus,$$
--   labelled (25:3:a), (25:3:b), (25:3:c), where $\ominus$ is the empty set and $-S$ the complement of $S$ in $I$.
--
--   Following 30.1.1:
--
--   1. An **imputation** is a vector $\vec\alpha = \{\alpha_1, \dots, \alpha_n\}$ with (30:1) $\alpha_i \geqq v((i))$ for $i = 1, \dots, n$ and (30:2) $\sum_{i=1}^n \alpha_i = 0$.
--   2. A set $S \subseteq I$ is **effective** for $\vec\alpha$ if (30:3) $\sum_{i \in S} \alpha_i \leqq v(S)$.
--   3. $\vec\alpha$ **dominates** $\vec\beta$, written $\vec\alpha \succ \vec\beta$, if there is a set $S$ with (30:4:a) $S$ not empty, (30:4:b) $S$ effective for $\vec\alpha$, (30:4:c) $\alpha_i > \beta_i$ for all $i \in S$.
--   4. A set $V$ of imputations is a **solution** if (30:5:a) no $\vec\beta$ in $V$ is dominated by an $\vec\alpha$ in $V$, and (30:5:b) every imputation $\vec\beta$ not in $V$ is dominated by some $\vec\alpha$ in $V$.
--
--   The **reduced form** of $v$ (27.1.4, (27:4)) is
--   $$\bar v(S) = v(S) + \sum_{k \in S} \Big(-v((k)) + \frac1n \sum_{j=1}^n v((j))\Big),$$
--   and the game is **inessential** (27.3.1) if $\bar v(S) \equiv 0$, **essential** (27.3.2) otherwise.
--
--   Chapter X works in this "old" theory of 30.1.1 (49.1.1): winning and losing coalitions, simplicity, and the main simple solution are all defined through these notions.
--
--   **Formalization Note** Players are `Fin n`, so the book's player $i$ is index $i-1$. Coalitions are `Finset (Fin n)`, $v$ is a function `Finset (Fin n) → ℝ`, imputations are vectors `Fin n → ℝ`. `Dominates v α β` is defined for arbitrary vectors; every statement restricts it to imputations as the book does. `IsSolution v V` requires every element of $V$ to be an imputation and quantifies (30:5:b) over imputations only. Essential is `¬ IsInessential v`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 241, 25.3.1, (25:3:a)–(25:3:c); pp. 263–264, 30.1.1, (30:1)–(30:5); p. 248, 27.1.4, (27:4); p. 249, 27.3.1–27.3.2

import Mathlib

namespace TheoryOfGames.SimpleGames

/-- The conditions (25:3:a)–(25:3:c) of 25.3.1 on a numerical set function `v` defined for all
subsets `S` of the set of players `I = Fin n` (the book's players `1, …, n` are `0, …, n - 1`;
`-S` is the complement `Sᶜ`):
* (25:3:a) `v(∅) = 0`;
* (25:3:b) `v(-S) = -v(S)`;
* (25:3:c) `v(S ∪ T) ≥ v(S) + v(T)` if `S ∩ T = ∅`.
These are the standing properties of the characteristic function of a zero-sum `n`-person game. -/
def IsCharFunction {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  v ∅ = 0 ∧
  (∀ S : Finset (Fin n), v Sᶜ = -v S) ∧
  (∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T))

/-- 30.1.1: an *imputation* is a vector `α = {α₁, …, αₙ}` with (30:1) `αᵢ ≧ v((i))` for
`i = 1, …, n` and (30:2) `∑ᵢ αᵢ = 0`. -/
def IsImputation {n : ℕ} (v : Finset (Fin n) → ℝ) (α : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, v {i} ≤ α i) ∧ ∑ i, α i = 0

/-- 30.1.1, (30:3): a set `S` of players is *effective* for `α` if `∑_{i in S} αᵢ ≦ v(S)`. -/
def IsEffective {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) (α : Fin n → ℝ) : Prop :=
  ∑ i ∈ S, α i ≤ v S

/-- 30.1.1, (30:4): `α` *dominates* `β`, `α ⊱ β`, if there exists a set `S` with
(30:4:a) `S` is not empty, (30:4:b) `S` is effective for `α`, (30:4:c) `αᵢ > βᵢ` for all `i`
in `S`. (The book applies the relation to imputations; every statement using it restricts
`α`, `β` to imputations.) -/
def Dominates {n : ℕ} (v : Finset (Fin n) → ℝ) (α β : Fin n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ IsEffective v S α ∧ ∀ i ∈ S, β i < α i

/-- 30.1.1, (30:5): a set `V` of imputations is a *solution* if
(30:5:a) no `β` in `V` is dominated by an `α` in `V`, and
(30:5:b) every imputation `β` not in `V` is dominated by some `α` in `V`. -/
def IsSolution {n : ℕ} (v : Finset (Fin n) → ℝ) (V : Set (Fin n → ℝ)) : Prop :=
  (∀ α ∈ V, IsImputation v α) ∧
  (∀ α ∈ V, ∀ β ∈ V, ¬ Dominates v α β) ∧
  (∀ β : Fin n → ℝ, IsImputation v β → β ∉ V → ∃ α ∈ V, Dominates v α β)

/-- 27.1.4, (27:2) with (27:4): the *reduced form* of `v`,
`v̄(S) = v(S) + ∑_{k in S} α⁰ₖ` with `α⁰ₖ = -v((k)) + (1/n) ∑_{j=1}^n v((j))`. -/
noncomputable def reducedForm {n : ℕ} (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  v S + ∑ k ∈ S, (-v {k} + (1 / (n : ℝ)) * ∑ j, v {j})

/-- 27.3.1: a game with characteristic function `v` is *inessential* if its reduced form is
`v̄(S) ≡ 0`; it is *essential* (27.3.2) otherwise, i.e. when `¬ IsInessential v`. -/
def IsInessential {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), reducedForm v S = 0

end TheoryOfGames.SimpleGames


