-- Prove2me | Definitions.Def_SilverRateLB_IsLocalHard
-- name    : SilverRateLB_IsLocalHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:14.030578+00:00
-- url     : https://prove2.me/theorems/4053f478-01eb-43b2-a328-7a1e0c2d5e66
-- title:
--   Local hard function: the conclusion of Lemma 3.2
-- statement:
--   Let $a,c$ be constants, $h_1,\dots,h_m$ gap stepsizes with $s=\sum_j h_j$, and $b$ a checkpoint stepsize. A pair $(f,\tau)$ with $f:\mathbb R^2\to\mathbb R$ and $\tau\in\mathbb R$ is a **local hard function** if
--
--   1. $\tau>0$, and $f$ is nonnegative, convex and $1$-smooth;
--   2. $f(x,y)=0$ for $x\le0$, $y\ge0$, and $\partial_2 f(x,y)=0$ for $x\in\mathbb R$, $y\ge\tau$ (property (8));
--   3. gradient descent on $f/2$ from $(x_0,y_0)=(1,0)$ with stepsizes $h_1,\dots,h_m,b$ satisfies
--   $$x_j>0,\quad 0\le y_j\le y_m=\tau-\frac{2}{c(a+s)}\quad(0\le j\le m),\qquad y_{m+1}=\tau+\frac{b-2}{c(a+s)}.$$
--
--   Lemma 3.2 asserts that such a pair exists for the constants of Lemma 2.4; the chain construction (9)–(11) uses only these properties.
--
--   **Formalization Note** $\partial_2 f$ is the second component of the gradient.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.2, p. 12

import Mathlib
import Definitions.Def_SilverRateLB_gdRun
import Definitions.Def_KatyushaNs_IsConvexLSmooth

namespace SilverRateLB

/-- The local GD iterates `(x_j, y_j)` of Lemma 3.2: GD on `f/2` from `(x_0, y_0) = (1, 0)` with
the stepsizes `h_1, …, h_m, b`, after `j` of them. -/
noncomputable def localIter (f : EuclideanSpace ℝ (Fin 2) → ℝ) (hs : List ℝ) (b : ℝ) (j : ℕ) :
    EuclideanSpace ℝ (Fin 2) :=
  gdRun (fun w => f w / 2) ((hs ++ [b]).take j) !₂[1, 0]

/-- **Local hard function** for the gap stepsizes `hs = (h_1, …, h_m)` and checkpoint step `b`:
the conclusion of Lemma 3.2 for a pair `(f, τ)`. With `s = ∑ h_j`:
1. `τ > 0`, and `f : ℝ² → ℝ` is nonnegative, convex and `1`-smooth;
2. (8): `f(x, y) = 0` for `x ≤ 0, y ≥ 0`, and `∂₂f(x, y) = 0` for `x ∈ ℝ, y ≥ τ`;
3. GD on `f/2` from `(1, 0)` with stepsizes `h_1, …, h_m, b` satisfies `x_j > 0`,
   `0 ≤ y_j ≤ y_m = τ − 2/(c(a + s))` for `0 ≤ j ≤ m`, and `y_{m+1} = τ + (b − 2)/(c(a + s))`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.2,
p. 12.

**Formalization Note** `ℝ²` is `EuclideanSpace ℝ (Fin 2)`, coordinate `0` is `x` and `1` is
`y`; `∂₂f` is the second component of Mathlib's `gradient`, the true partial derivative because
`f` is differentiable. The constants `a, c` are parameters (Lemma 3.2 uses those of Lemma 2.4). -/
def IsLocalHard (a c : ℝ) (hs : List ℝ) (b : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (τ : ℝ) :
    Prop :=
  0 < τ ∧ (∀ z, 0 ≤ f z) ∧ KatyushaNs.IsConvexLSmooth 1 f ∧
    (∀ x y : ℝ, x ≤ 0 → 0 ≤ y → f !₂[x, y] = 0) ∧
    (∀ x y : ℝ, τ ≤ y → gradient f !₂[x, y] 1 = 0) ∧
    (∀ j ≤ hs.length, 0 < localIter f hs b j 0 ∧ 0 ≤ localIter f hs b j 1 ∧
      localIter f hs b j 1 ≤ localIter f hs b hs.length 1) ∧
    localIter f hs b hs.length 1 = τ - 2 / (c * (a + hs.sum)) ∧
    localIter f hs b (hs.length + 1) 1 = τ + (b - 2) / (c * (a + hs.sum))

end SilverRateLB


