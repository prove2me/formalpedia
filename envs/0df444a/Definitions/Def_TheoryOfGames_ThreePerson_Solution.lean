-- Prove2me | Definitions.Def_TheoryOfGames_ThreePerson_Solution
-- name    : TheoryOfGames_ThreePerson_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T08:09:16.633755+00:00
-- url     : https://prove2.me/theorems/a85fe86f-2406-4edf-bbd4-95a3d7c8ade4
-- title:
--   Imputations, effective sets, domination and solutions of a zero-sum n-person game (30.1.1)
-- statement:
--   Let $I = \{1, \dots, n\}$ be the set of players of a zero-sum $n$-person game and let $v(S)$ be a numerical function defined for all subsets $S \subseteq I$. The standing properties of a **characteristic function** (25.3.1) are
--   $$v(\ominus) = 0, \qquad v(-S) = -v(S), \qquad v(S \cup T) \geqq v(S) + v(T) \text{ if } S \cap T = \ominus,$$
--   labelled (25:3:a), (25:3:b), (25:3:c), where $\ominus$ is the empty set and $-S$ the complement of $S$ in $I$.
--
--   Following 30.1.1:
--
--   1. An **imputation** (or distribution) is a vector $\vec\alpha = \{\alpha_1, \dots, \alpha_n\}$ with (30:1) $\alpha_i \geqq v((i))$ for $i = 1, \dots, n$ and (30:2) $\sum_{i=1}^n \alpha_i = 0$.
--   2. A set $S \subseteq I$ is **effective** for $\vec\alpha$ if (30:3) $\sum_{i \in S} \alpha_i \leqq v(S)$.
--   3. $\vec\alpha$ **dominates** $\vec\beta$, written $\vec\alpha \succ \vec\beta$, if there is a set $S$ with (30:4:a) $S$ not empty, (30:4:b) $S$ effective for $\vec\alpha$, (30:4:c) $\alpha_i > \beta_i$ for all $i \in S$.
--   4. A set $V$ of imputations is a **solution** if (30:5:a) no $\vec\beta$ in $V$ is dominated by an $\vec\alpha$ in $V$, and (30:5:b) every imputation $\vec\beta$ not in $V$ is dominated by some $\vec\alpha$ in $V$.
--
--   These are the basic notions of the book's general theory of zero-sum $n$-person games; every result of Chapter VI from §30 on is stated in terms of them. A solution is what later literature calls a von Neumann–Morgenstern stable set.
--
--   **Formalization Note** Players are `Fin n`, so the book's player $i$ is index $i-1$. Coalitions are `Finset (Fin n)`, $v$ is a function `Finset (Fin n) → ℝ`, and imputations are vectors `Fin n → ℝ`. `IsCharFunction v` bundles (25:3:a)–(25:3:c). `Dominates v α β` is defined for arbitrary vectors; every theorem restricts it to imputations as the book does. `IsSolution v V` requires every element of $V$ to be an imputation, and quantifies (30:5:b) over imputations only.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 263–264, 30.1.1, (30:1)–(30:5); p. 241, 25.3.1, (25:3:a)–(25:3:c)

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

namespace TheoryOfGames.ThreePerson

/-- 30.1.1: a *distribution* or *imputation* is a vector `α = {α₁, …, αₙ}` with
(30:1) `αᵢ ≧ v((i))` for `i = 1, …, n` and (30:2) `∑ᵢ αᵢ = 0`. -/
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

end TheoryOfGames.ThreePerson


