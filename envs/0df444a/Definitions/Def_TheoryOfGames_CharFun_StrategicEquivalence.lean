-- Prove2me | Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence
-- name    : TheoryOfGames_CharFun_StrategicEquivalence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T03:42:08.41816+00:00
-- url     : https://prove2.me/theorems/2d966002-ebe7-47d6-9e45-f3e8cbc6377b
-- title:
--   Strategic equivalence, reduced characteristic functions, the reduced form, inessential and essential games (§27)
-- statement:
--   Let $I = \{1, \dots, n\}$ and let $v, v'$ be numerical set functions on the subsets of $I$. Write $(k)$ for the one-element set $\{k\}$.
--
--   1. **Strategic equivalence** (27.1.1–27.1.2): $v'$ is strategically equivalent to $v$ if there is a system of numbers $\alpha^0_1, \dots, \alpha^0_n$ with (27:1) $\sum_{k=1}^n \alpha^0_k = 0$ such that (27:2)
--   $$v'(S) \equiv v(S) + \sum_{k \in S} \alpha^0_k .$$
--   2. **Reduced** (27:3): $\bar v$ is reduced if $\bar v((1)) = \bar v((2)) = \cdots = \bar v((n))$.
--   3. **Reduced form** (27:A): $\bar v$ is obtained from $v$ by (27:2) with the system (27:4) $\alpha^0_k = -v((k)) + \frac1n \sum_{j=1}^n v((j))$, i.e.
--   $$\bar v(S) = v(S) + \sum_{k \in S}\Big(-v((k)) + \frac1n \sum_{j=1}^n v((j))\Big).$$
--   4. **Inessential** (27.3.1): the game (with characteristic function $v$) is inessential if its reduced form is $\bar v(S) \equiv 0$.
--   5. **Essential** (27.3.2): the game is essential if its reduced form is not $\equiv 0$.
--
--   These notions are properties of the set function $v$ alone; they organize the analysis of characteristic functions in §27 and the rest of the book.
--
--   **Formalization Note** Players are `Fin n` and coalitions `Finset (Fin n)`. In the reduced form the factor $\frac1n$ is the real number `1 / n`; for $n = 0$ it is $0$, which does not matter because then every sum over players is empty.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 245–248, 27.1.1–27.1.4, (27:1)–(27:4), (27:A); pp. 249–250, 27.3.1, 27.3.2

import Mathlib

namespace TheoryOfGames.CharFun

variable {n : ℕ}

/-- Strategic equivalence (27.1.1–27.1.2): `v'` arises from `v` by (27:2)
`v'(S) = v(S) + ∑_{k ∈ S} α⁰_k` for a system `α⁰₁, …, α⁰ₙ` with (27:1) `∑_{k=1}^n α⁰_k = 0`. -/
def StrategicallyEquivalent (v v' : Finset (Fin n) → ℝ) : Prop :=
  ∃ α : Fin n → ℝ, ∑ k, α k = 0 ∧ ∀ S : Finset (Fin n), v' S = v S + ∑ k ∈ S, α k

/-- (27:3): `v̄` is *reduced* if every one-element coalition has the same value,
`v̄((1)) = v̄((2)) = ⋯ = v̄((n))`. -/
def IsReduced (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ j k : Fin n, v {j} = v {k}

/-- The reduced form of `v` (27:A): (27:2) with the system (27:4)
`α⁰_k = -v((k)) + (1/n) ∑_{j=1}^n v((j))`, i.e.
`v̄(S) = v(S) + ∑_{k ∈ S} (-v((k)) + (1/n) ∑_{j=1}^n v((j)))`. -/
noncomputable def reducedForm (v : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  v S + ∑ k ∈ S, (-v {k} + (1 / (n : ℝ)) * ∑ j : Fin n, v {j})

/-- 27.3.1: a game (with characteristic function `v`) is *inessential* if its reduced form is
`v̄(S) ≡ 0`. -/
def IsInessential (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), reducedForm v S = 0

/-- 27.3.2: a game is *essential* if its reduced form is not `≡ 0`. -/
def IsEssential (v : Finset (Fin n) → ℝ) : Prop :=
  ¬ IsInessential v

end TheoryOfGames.CharFun


