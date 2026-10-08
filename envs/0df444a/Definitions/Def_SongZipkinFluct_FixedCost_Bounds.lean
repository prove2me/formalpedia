-- Prove2me | Definitions.Def_SongZipkinFluct_FixedCost_Bounds
-- name    : SongZipkinFluct_FixedCost_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:52.89679+00:00
-- url     : https://prove2.me/theorems/76bf7e0e-668d-473b-9b8a-34d21e8526d8
-- title:
--   Definition 2 (K-convexity on ℤ), the (r, S) parameters of Theorem 3(b), and the bounds y⁺, y⁺_min, y*, S⁺, r⁺, r⁻, r⁻⁻ of p. 358
-- statement:
--   **Definition 2 ($l$-convexity on the integers).** Let $f : \mathbb Z \to \mathbb R$ and $l \ge 0$. Then $f$ is **$l$-convex** if for all integers $x$ and all positive integers $a, b$,
--   $$
--   \frac{f(x) - f(x-b)}{b}\,a + f(x) \le f(x+a) + l.
--   $$
--
--   **Minimizers and the $(r, S)$ parameters.** For $f : \mathbb Z \to \mathbb R$ and $K$, the pair $(r, S)$ is the $(r, S)$ pair of $f$ if $S$ is the smallest global minimizer of $f$ and $r$ is the largest $y < S$ with $f(y) > K + f(S)$. For the fixed-cost iterates, $S^*_n(i)$, $r^*_n(i)$ ($n \ge 1$) are the $(r, S)$ pair of $G_n(i, \cdot)$.
--
--   **The bounds of p. 358.** Let $y^+(i)$ be the smallest minimizer of $G^+(i, \cdot)$, $y^+_{\min} = \min_i y^+(i)$, and $y^*(i)$ the smallest minimizer of $G_0(i, \cdot)$ (the optimal basestock level of the linear model). Then
--   $$
--   \begin{aligned}
--   S^+(i) &= \min\{y \ge y^+(i) : G^+(i, y) - G^+(i, y^+(i)) > \gamma K\},\\
--   r^+(i) &= \max\{y < y^+(i) : G^+(i, y) - G^+(i, y^+(i)) > (1-\gamma)K\},\\
--   r^-(i) &= \max\{y < y^*(i) : G_0(i, y) - G_0(i, y^*(i)) > K\},\\
--   r^{--}(i) &= \max\{y < y^+_{\min} : G^+(i, y) - G^+(i, y^+_{\min}) > K\}.
--   \end{aligned}
--   $$
--
--   These are the quantities of the bounds theorems (Theorems 4 and 6): they are computed from the myopic cost $G^+$ and the linear model alone, and bracket the optimal $(r, S)$ parameters of the fixed-cost model.
--
--   **Formalization Note** Each minimizer and each extremal integer is a predicate on a candidate value (least or greatest element of the defining set), never `sInf`/`sSup` on $\mathbb Z$, which would return junk on empty or unbounded sets. Definition 2 is K-convexity on $\mathbb Z$; it is not the K-convexity on $\mathbb R$ of other platform items.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 356 (y⁺); p. 357 (y⁺_min, Theorem 2(b) y*); p. 358, Definition 2, Theorem 3(b), definitions of S⁺, r⁺, r⁻, r⁻⁻

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Recursion

namespace SongZipkinFluct.FixedCost

open Model

/-- Definition 2 (p. 358): for `l ≥ 0`, a function `f : ℤ → ℝ` is **`l`-convex** if, for all
integers `x` and all positive integers `a`, `b`,
`(f(x) − f(x − b))/b · a + f(x) ≤ f(x + a) + l`.

Formalization Note: the paper requires `l ≥ 0` as part of the definition; every use below has
`l = K = K̄ F̃_L(α) > 0`. -/
def LConvex (l : ℝ) (f : ℤ → ℝ) : Prop :=
  ∀ x a b : ℤ, 0 < a → 0 < b → (f x - f (x - b)) / (b : ℝ) * (a : ℝ) + f x ≤ f (x + a) + l

/-- `y` is the smallest global minimizer of `f : ℤ → ℝ`. -/
def IsSmallestMin (f : ℤ → ℝ) (y : ℤ) : Prop := IsLeast {z | ∀ w, f z ≤ f w} y

/-- The `(r, S)` parameters of Theorem 3(b) (p. 358) for a function `f = G_n(i, ·)` and a fixed
cost `K`: `S` is the smallest global minimizer of `f`, and `r` is the largest `y < S` with
`f(y) > K + f(S)`. -/
def IsRSParams (K : ℝ) (f : ℤ → ℝ) (r S : ℤ) : Prop :=
  IsSmallestMin f S ∧ IsGreatest {y | y < S ∧ K + f S < f y} r

variable {I : Type*} [DecidableEq I]

/-- `y⁺(i)` = the smallest value of `y` that minimizes `G⁺(i, y)`, for every `i` (p. 356). -/
def IsYPlus (M : Model I) (yplus : I → ℤ) : Prop := ∀ i, IsSmallestMin (M.Gplus i) (yplus i)

/-- `y⁺_min = min_{i ∈ I} y⁺(i)` (p. 357). -/
def IsYPlusMin (yplus : I → ℤ) (ymin : ℤ) : Prop := IsLeast (Set.range yplus) ymin

/-- `y*(i)` = the smallest value of `y` that minimizes `G₀(i, y) = G_∞(i, y)` of the linear
order-cost model (Theorem 2(b), p. 357), for every `i`. -/
def IsYStar (M : Model I) (ystar : I → ℤ) : Prop := ∀ i, IsSmallestMin (Glin M i) (ystar i)

/-- `S⁺(i) = min{y ≥ y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > γK}` (p. 358), for every `i`. -/
def IsSPlus (M : Model I) (yplus Splus : I → ℤ) : Prop :=
  ∀ i, IsLeast {y | yplus i ≤ y ∧ M.γ * M.K < M.Gplus i y - M.Gplus i (yplus i)} (Splus i)

/-- `r⁺(i) = max{y < y⁺(i) : G⁺(i, y) − G⁺(i, y⁺(i)) > (1 − γ)K}` (p. 358), for every `i`. -/
def IsRPlus (M : Model I) (yplus rplus : I → ℤ) : Prop :=
  ∀ i, IsGreatest {y | y < yplus i ∧ (1 - M.γ) * M.K < M.Gplus i y - M.Gplus i (yplus i)}
    (rplus i)

/-- `r⁻(i) = max{y < y*(i) : G₀(i, y) − G₀(i, y*(i)) > K}` (p. 358), for every `i`. -/
def IsRMinus (M : Model I) (ystar rminus : I → ℤ) : Prop :=
  ∀ i, IsGreatest {y | y < ystar i ∧ M.K < Glin M i y - Glin M i (ystar i)} (rminus i)

/-- `r⁻⁻(i) = max{y < y⁺_min : G⁺(i, y) − G⁺(i, y⁺_min) > K}` (p. 358), for every `i`. -/
def IsRMinusMinus (M : Model I) (ymin : ℤ) (rmm : I → ℤ) : Prop :=
  ∀ i, IsGreatest {y | y < ymin ∧ M.K < M.Gplus i y - M.Gplus i ymin} (rmm i)

/-- `S*_n(i)`, `r*_n(i)` of Theorem 3(b) (p. 358) for the fixed-cost iterates, for every
`n ≥ 1` and every `i` (the values at `n = 0` are not constrained). -/
def IsStageParams (M : Model I) (rs Ss : ℕ → I → ℤ) : Prop :=
  ∀ n, 1 ≤ n → ∀ i, IsRSParams M.K (Gfix M n i) (rs n i) (Ss n i)

end SongZipkinFluct.FixedCost


