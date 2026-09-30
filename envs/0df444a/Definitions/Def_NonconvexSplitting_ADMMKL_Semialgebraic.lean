-- Prove2me | Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
-- name    : NonconvexSplitting_ADMMKL_Semialgebraic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T18:09:45.624378+00:00
-- url     : https://prove2.me/theorems/266423a6-03a9-44d5-b3bd-ff9346e9b4a4
-- title:
--   Semi-algebraic sets and functions
-- statement:
--   A set $S\subseteq\mathbb R^N$ is **semi-algebraic** if it is a finite union of sets of the form
--   $$
--   \{v\in\mathbb R^N:\ p_1(v)=\cdots=p_k(v)=0,\ g_1(v)<0,\dots,g_l(v)<0\},
--   $$
--   where $p_1,\dots,p_k,g_1,\dots,g_l$ are real polynomials in $N$ variables ($k,l\ge0$).
--
--   A function $f:\mathbb R^N\to(-\infty,+\infty]$ is **semi-algebraic** if its graph $\{(u,r)\in\mathbb R^N\times\mathbb R:\ f(u)=r\}$ is a semi-algebraic subset of $\mathbb R^{N+1}$.
--
--   Semi-algebraicity is the easily checked sufficient condition for the KL property used in Theorem 3; polynomials, indicators of semi-algebraic sets and the $\ell_0$ "norm" are semi-algebraic.
--
--   **Formalization Note** The paper defines semi-algebraicity for real-valued maps via $\operatorname{gph}F\subseteq\mathbb R^{N+1}$. For an extended-valued $f$ the graph is taken over its real values (over $\operatorname{dom} f$), the standard reading for proper functions (Attouch–Bolte–Redont–Soubeyran 2010, §4.3); for real-valued $f$ (coerced to `EReal`) it is the paper's definition. The last coordinate of $v\in\mathbb R^{N+1}$ is the value and the first $N$ coordinates are the argument.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 4, definition of semi-algebraic sets and maps

import Mathlib

namespace NonconvexSplitting.ADMMKL

/-- A semi-algebraic subset of `ℝᴺ` (Li–Pong, p. 4): a finite union of basic sets
`{v | p₁(v) = ⋯ = p_k(v) = 0, g₁(v) < 0, …, g_l(v) < 0}` with real polynomials `pᵢ, gⱼ` in
`N` variables (`k, l ≥ 0`; the empty union is allowed). -/
def IsSemialgebraicSet {N : ℕ} (S : Set (Fin N → ℝ)) : Prop :=
  ∃ (K : ℕ) (eqs lts : Fin K → Finset (MvPolynomial (Fin N) ℝ)),
    S = ⋃ i, {v | (∀ p ∈ eqs i, MvPolynomial.eval v p = 0) ∧
      ∀ g ∈ lts i, MvPolynomial.eval v g < 0}

/-- A function `f : ℝᴺ → (-∞, +∞]` is semi-algebraic (Li–Pong, p. 4) if its graph over its
real values, `{(u, r) ∈ ℝᴺ × ℝ | f(u) = r}`, is a semi-algebraic subset of `ℝᴺ⁺¹`; the last
coordinate of `v : Fin (N+1) → ℝ` is the value `r` and the first `N` are `u`. For real-valued
`f` (coerced to `EReal`) this is the paper's definition verbatim; for extended-valued `f` it is
the graph over `dom f`. -/
def IsSemialgebraicFn {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → EReal) : Prop :=
  IsSemialgebraicSet {v : Fin (N + 1) → ℝ |
    f (WithLp.toLp 2 (Fin.init v)) = ((v (Fin.last N) : ℝ) : EReal)}

end NonconvexSplitting.ADMMKL


