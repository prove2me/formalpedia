-- Prove2me | Definitions.Def_BellmanDP_Games_MinMax
-- name    : BellmanDP_Games_MinMax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T20:14:09.628529+00:00
-- url     : https://prove2.me/theorems/ba163aff-dcd9-4cb9-887f-089c0fdc8163
-- title:
--   Max-min equals min-max with attained extrema; the bilinear form $\sum_{i,j} a_{ij}p_iq_j$; the survival-game payoff
-- statement:
--   This file fixes the vocabulary of finite two-person zero-sum games used throughout Bellman's Chapter X.
--
--   1. **Max-min equals min-max.** For a payoff function $K(x,y)$, a set $X$ of choices of the maximizing player and a set $Y$ of choices of the minimizing player, the predicate "the game has value $v$" means
--   $$\max_{x\in X}\ \min_{y\in Y} K(x,y) \;=\; v \;=\; \min_{y\in Y}\ \max_{x\in X} K(x,y),$$
--   where every maximum and minimum is attained: some $x\in X$ has $\min_y K(x,y)=v$ and no $x$ has an attained minimum above $v$; symmetrically for $\min_y\max_x$.
--   2. **The bilinear form.** For a matrix $A=(a_{ij})$ and vectors $p,q$, the expected return $E_A(p,q)=\sum_{i,j} a_{ij}\,p_i\,q_j$ (Bellman, § 2, Eq. (2.2)).
--   3. **The survival-game payoff.** For integers $a,b,c$, a function $f:\mathbb Z\to\mathbb R$, an integer $x$ and two-point distribution vectors $p=(p_1,p_2)$, $q=(q_1,q_2)$,
--   $$T(p,q,f)(x) = p_1q_1 f(x-1) + p_1q_2 f(x+a) + p_2q_1 f(x+c) + p_2q_2 f(x-b),$$
--   the bracket of Chapter X, Theorem 5, Eq. (19.1).
--
--   These objects are shared by the goal theorem (the extended min-max theorem) and by the games-of-survival theorem.
--
--   **Formalization Note** The value predicate asserts attainment explicitly (`IsGreatest` / `IsLeast` of the sets of attained minima and maxima) instead of using `sSup`/`sInf`, which in Lean return $0$ on empty or unbounded sets. In the survival payoff the two coordinates of $p$ are `p 0` $=p_1$ and `p 1` $=p_2$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 2, Eqs. (2.2)-(2.3), p. 285; § 3, Eq. (3.3), p. 285; § 11, Eq. (11.1), p. 294; Theorem 5, Eq. (19.1), p. 303

import Mathlib

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, § 3, Eq. (3.3), p. 285 and § 11, Eq. (11.1), p. 294:
the statement "`Max_x Min_y K(x, y) = Min_y Max_x K(x, y)`, and the common value is `v`", with
every maximum and minimum attained.

* The first clause says that for some `x ∈ X` the minimum of `y ↦ K(x, y)` over `Y` is attained
  and equals `v`, and that no `x ∈ X` has an attained minimum above `v`: `v = Max_x Min_y K`.
* The second clause says the same for `Min_y Max_x K`.

Nothing is assumed about `K`, `X`, `Y`: the predicate asserts attainment rather than relying on
`sSup`/`sInf` of possibly empty or unbounded sets. -/
def IsMaxMinMinMaxValue {α β : Type*} (K : α → β → ℝ) (X : Set α) (Y : Set β) (v : ℝ) :
    Prop :=
  IsGreatest {w | ∃ x ∈ X, IsLeast ((fun y => K x y) '' Y) w} v ∧
    IsLeast {w | ∃ y ∈ Y, IsGreatest ((fun x => K x y) '' X) w} v

/-- Ch. X, § 2, Eqs. (2.2)–(2.3), p. 285: the bilinear form `Σ_{i,j} a_ij p_i q_j` of a matrix
`A = (a_ij)` evaluated at the vectors `p` and `q` (the expected return when the players use the
distribution vectors `p`, `q`). -/
def bilin {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (p : ι → ℝ) (q : κ → ℝ) :
    ℝ :=
  ∑ i, ∑ j, A i j * p i * q j

/-- The bilinear form of Ch. X, Theorem 5, Eq. (19.1), p. 303, at the integer `x`:
`p₁q₁ f(x − 1) + p₁q₂ f(x + a) + p₂q₁ f(x + c) + p₂q₂ f(x − b)`, with `p = (p₁, p₂)` indexed by
`Fin 2` (`p 0 = p₁`, `p 1 = p₂`), and likewise `q`. -/
def survivalPayoff (a b c : ℤ) (f : ℤ → ℝ) (x : ℤ) (p q : Fin 2 → ℝ) : ℝ :=
  p 0 * q 0 * f (x - 1) + p 0 * q 1 * f (x + a) + p 1 * q 0 * f (x + c) + p 1 * q 1 * f (x - b)

end BellmanDP.Games


