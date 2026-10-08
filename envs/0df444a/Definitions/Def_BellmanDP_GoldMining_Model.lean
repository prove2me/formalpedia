-- Prove2me | Definitions.Def_BellmanDP_GoldMining_Model
-- name    : BellmanDP_GoldMining_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T14:59:30.057982+00:00
-- url     : https://prove2.me/theorems/23f5ff67-79a8-4882-b3a6-281ae61ac110
-- title:
--   The stochastic gold-mining equation $f(x,y)=\max[p_1(r_1x+f((1-r_1)x,y)),\,p_2(r_2y+f(x,(1-r_2)y))]$, its finite-stage returns and decision regions
-- statement:
--   This file sets up Bellman's two-mine stochastic gold-mining process. Anaconda holds an amount $x \ge 0$ of gold and Bonanza an amount $y \ge 0$. One machine is used at a time: in Anaconda it mines the fraction $r_1$ of the gold there and stays in working order with probability $p_1$ (and is destroyed, mining nothing, otherwise); in Bonanza the corresponding data are $r_2$ and $p_2$.
--
--   1. The return of an A-choice followed by a continuation $f$ (Bellman's (4.3)), and of a B-choice (4.4):
--   $$A_f(x,y) = p_1\bigl[r_1x + f((1-r_1)x,\,y)\bigr], \qquad B_f(x,y) = p_2\bigl[r_2y + f(x,\,(1-r_2)y)\bigr].$$
--   2. A function $f$ **solves (5.1)** when, for all $x, y \ge 0$,
--   $$f(x,y) = \max\bigl(A_f(x,y),\,B_f(x,y)\bigr).$$
--   3. The function class of Chapter II, Theorem 1: $f$ is **bounded in every rectangle** $0 \le x \le \bar X$, $0 \le y \le \bar Y$.
--   4. The $N$-stage returns (4.2), (4.5): $f_0 = 0$ and $f_{N+1}(x,y) = \max\bigl(A_{f_N}(x,y),\,B_{f_N}(x,y)\bigr)$, so that $f_1(x,y) = \max(p_1r_1x,\,p_2r_2y)$ is the book's one-stage return.
--   5. The **decision regions** (§ 8) of a value function $v$ with continuation $f$: the A-region is the set of points of the closed quadrant where $v = A_f$, the B-region the set where $v = B_f$. For the infinite process $v = f$; for the $(N+1)$-stage process $v = f_{N+1}$ and the continuation is $f_N$.
--   6. The perturbed equation of Theorem 7: $g(x,y) = \max\bigl(A_g(x,y),\,B_g(x,y)\bigr) + h(x,y)$ for $x, y \ge 0$.
--
--   These objects are shared by Theorems 1, 2, 5, 6 and 7 of the chapter.
--
--   **Formalization Note** Functions are `ℝ → ℝ → ℝ`; only their values on the closed quadrant matter. The index $N$ of the book's $f_N$ ($N \ge 1$) is the Lean `goldIter … N`, with the extra value `goldIter … 0 = 0` chosen so that the recursion also produces $f_1$. A point is in both regions exactly when the two choices tie.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 4, Eqs. (4.2)-(4.5), p. 63; § 5, Eq. (5.1), p. 63; § 6, Theorem 1, p. 64; § 8, p. 66; § 14, Theorem 7, Eq. (2), p. 76

import Mathlib

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, § 4, Eq. (4.3), and § 5, Eq. (5.1), p. 63: the
return of an A-choice (use the machine in Anaconda) at amounts `x` (Anaconda), `y` (Bonanza),
followed by the continuation `f`: `p₁ [r₁ x + f((1 − r₁) x, y)]`. -/
def goldA (p₁ r₁ : ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p₁ * (r₁ * x + f ((1 - r₁) * x) y)

/-- Ch. II, § 4, Eq. (4.4), and § 5, Eq. (5.1), p. 63: the return of a B-choice (use the machine
in Bonanza) followed by the continuation `f`: `p₂ [r₂ y + f(x, (1 − r₂) y)]`. -/
def goldB (p₂ r₂ : ℝ) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  p₂ * (r₂ * y + f x ((1 - r₂) * y))

/-- Ch. II, § 5, Eq. (5.1), p. 63: `f` satisfies
`f(x, y) = Max [p₁ (r₁ x + f((1 − r₁) x, y)), p₂ (r₂ y + f(x, (1 − r₂) y))]` for all `x, y ≥ 0`. -/
def IsGoldMiningSolution (p₁ p₂ r₁ r₂ : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f x y = max (goldA p₁ r₁ f x y) (goldB p₂ r₂ f x y)

/-- Ch. II, Theorem 1, p. 64: the function class of the theorem, "bounded in any rectangle
`0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`". -/
def BoundedOnRectangles (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ X Y : ℝ, ∃ M : ℝ, ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |f x y| ≤ M

/-- Ch. II, § 4, Eqs. (4.2) and (4.5), p. 63, and § 12, Theorem 5, Eq. (1), p. 72: the `N`-stage
returns. `goldIter … 0 = 0`, so that `goldIter … 1 = Max [p₁ r₁ x, p₂ r₂ y]` is the book's `f₁`,
and `goldIter … (N + 1) = Max [A: p₁ [r₁ x + f_N((1 − r₁) x, y)], B: p₂ [r₂ y + f_N(x, (1 − r₂) y)]]`
is the book's `f_{N+1}`. -/
noncomputable def goldIter (p₁ p₂ r₁ r₂ : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ _ => 0
  | N + 1 => fun x y =>
      max (goldA p₁ r₁ (goldIter p₁ p₂ r₁ r₂ N) x y) (goldB p₂ r₂ (goldIter p₁ p₂ r₁ r₂ N) x y)

/-- Ch. II, § 8, p. 66 ("decision regions"): the set of points of the closed quadrant at which the
A-choice is an optimal first choice, for the value function `v` whose continuation is `f`, i.e.
where `v(x, y) = p₁ [r₁ x + f((1 − r₁) x, y)]`. For the infinite process `v = f`; for the
`(N + 1)`-stage process `v = f_{N+1}` and `f = f_N`. -/
def regionA (p₁ r₁ : ℝ) (f v : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ v z.1 z.2 = goldA p₁ r₁ f z.1 z.2}

/-- Ch. II, § 8, p. 66: the set of points of the closed quadrant at which the B-choice is an
optimal first choice, for the value function `v` whose continuation is `f`. -/
def regionB (p₂ r₂ : ℝ) (f v : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ v z.1 z.2 = goldB p₂ r₂ f z.1 z.2}

/-- Ch. II, § 14, Theorem 7, Eq. (2), p. 76: `g` satisfies the perturbed equation
`g(x, y) = Max [A: p₁ [r₁ x + g((1 − r₁) x, y)], B: p₂ [r₂ y + g(x, (1 − r₂) y)]] + h(x, y)`
for all `x, y ≥ 0`. -/
def IsPerturbedSolution (p₁ p₂ r₁ r₂ : ℝ) (h g : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = max (goldA p₁ r₁ g x y) (goldB p₂ r₂ g x y) + h x y

end BellmanDP.GoldMining


