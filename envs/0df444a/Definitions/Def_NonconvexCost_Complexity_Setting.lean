-- Prove2me | Definitions.Def_NonconvexCost_Complexity_Setting
-- name    : NonconvexCost_Complexity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:07.757987+00:00
-- url     : https://prove2.me/theorems/d62cfad6-e43d-40c5-a927-79879fb5c302
-- title:
--   §2–§6, pp. 2–16 — directional subgradient maps, Goldstein subgradients, shortest vectors, concave deviation, nonconvexity modulus, bisection (Algorithm 3.1)
-- statement:
--   Let $X$ be a real inner product space with norm $|\cdot|$; $X$ need be neither finite-dimensional nor complete. This file fixes the objects of Kong and Lewis's analysis.
--
--   1. **Directional subgradient map on $C$** (§2, p. 2). Given $C\subset X$, a map $G\colon X\times X\to X$ is a directional subgradient map for $f$ on $C$ if, for every $x\in C$ and every direction $e\in X$ such that $x+te\in C$ for all small $t\ge0$, the Gâteaux directional derivative exists and equals
--   $$f'(x;e)=\lim_{t\downarrow0}\frac{f(x+te)-f(x)}{t}=\langle G(x,e),e\rangle .$$
--   2. **$L$-boundedness** (p. 2): $L>0$ and $|G(x,e)|\le L$ for all $x,e\in X$.
--   3. **Goldstein subgradients** (p. 4): for $\delta>0$, $\partial_\delta f(x)$ is the set of convex combinations $\sum_{i=1}^k\lambda_i G(x_i,e_i)$ with $x_i$ in the closed ball $B_\delta(x)$ and $e_i\in X$ arbitrary, i.e. the convex hull of $\{G(y,e): |y-x|\le\delta,\ e\in X\}$.
--   4. **Shortest vector in a segment**: $g''$ is a shortest vector in $[g,g']$ if $g''\in[g,g']$ and $|g''|\le|v|$ for all $v\in[g,g']$. The closed form used by the algorithm is
--   $$\operatorname{short}(g,g')=g+\tau(g'-g),\qquad \tau=\max\Big\{0,\min\Big\{1,\frac{\langle g,g-g'\rangle}{|g-g'|^2}\Big\}\Big\}$$
--   (with $\tau=0$ when $g=g'$).
--   5. **Concave deviation** (Definition 5.4, p. 13): for an interval $J\subset\mathbb R$ and $h\colon J\to\mathbb R$, the infimum of the Lipschitz constants of convex functions $s\colon J\to\mathbb R$ such that $h+s$ is convex on $J$; it is $+\infty$ when no such $s$ exists.
--   6. **Nonconvexity modulus** (6.1), p. 16: for $f$ on $C$ and $\delta>0$,
--   $$\Lambda(\delta)=\sup\big\{\text{concave deviation of } t\mapsto f\big(x+\tfrac t\delta(y-x)\big) \text{ on } [0,\delta]\ :\ x,y\in C,\ |x-y|\le\delta\big\}\in[0,+\infty].$$
--   7. **Bisection** (Algorithm 3.1, p. 6) on $[p,q]$ for $h$ with right derivative $h'_+$: evaluate $h'_+(p)$, then repeatedly evaluate $h'_+$ at the midpoint $m$ of the current interval $[l,r]$, stopping as soon as a value is negative, and otherwise keeping $[l,m]$ if $2h(m)<h(l)+h(r)$ and $[m,r]$ otherwise. The file records the successive intervals, the successive evaluation points ($p$, then the midpoints), the predicate "the first $k$ evaluations are all nonnegative" (the method evaluates $h'_+$ $k$ times without terminating), and the predicate "$h'$ is the finite right derivative of $h$ at every point of $[p,q)$".
--
--   These objects are shared by every statement of the mission: the goal theorem is a bound on the run of Algorithm 4.1 expressed through $\Lambda(\delta)$, and the univariate milestones are statements about the bisection and the concave deviation.
--
--   **Formalization Note** $f$ is a function on all of $X$, but only its values on $C$ enter the definitions of the directional subgradient map (only feasible directions at points of $C$) and of $\Lambda$. The concave deviation and $\Lambda$ take values in $[0,+\infty]$ (`ℝ≥0∞`). The bisection's comparison uses $h(l)+h(r)$, as in (5.3) on p. 11; Algorithm 3.1 as printed reads $f(l)+f(r)$, a typo. The right derivative is passed as a function together with `HasDerivWithinAt` on $[t,q]$, never read off `derivWithin`.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, pp. 2–16, §2 (p. 2 directional subgradient map, L-bounded; p. 4 Goldstein subgradients), Algorithm 3.1 (p. 6), Definition 5.4 (p. 13), (6.1) (p. 16)

import Mathlib

namespace NonconvexCost.Complexity

open Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- §2, p. 2, restricted to `C` (in Theorem 6.6 `f : C → ℝ`): `G` is a directional subgradient map
for `f` on `C` if at every `x ∈ C`, along every direction `e` with `x + t e ∈ C` for all small
`t ≥ 0`, the Gâteaux directional derivative `f'(x; e) = lim_{t ↓ 0} (f(x + t e) - f x) / t` exists
and equals `⟪G x e, e⟫`. -/
def IsDirSubgradMapOn (f : X → ℝ) (G : X → X → X) (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ e : X, (∃ τ > 0, ∀ t ∈ Icc (0 : ℝ) τ, x + t • e ∈ C) →
    Tendsto (fun t : ℝ => (f (x + t • e) - f x) / t) (𝓝[>] 0) (𝓝 ⟪G x e, e⟫)

/-- §2, p. 2: `G` is `L`-bounded, for a constant `L > 0`: `‖G x e‖ ≤ L` for all `x, e`. -/
def IsLBounded (G : X → X → X) (L : ℝ) : Prop :=
  0 < L ∧ ∀ x e : X, ‖G x e‖ ≤ L

/-- §2, p. 4: the set `∂_δ f(x)` of Goldstein subgradients at `x`, the convex combinations of
vectors `G(y, e)` with `y` in the closed ball of radius `δ` around `x` and `e ∈ X` arbitrary. -/
def goldstein (G : X → X → X) (δ : ℝ) (x : X) : Set X :=
  convexHull ℝ {v | ∃ y e : X, ‖y - x‖ ≤ δ ∧ v = G y e}

/-- `g''` is a shortest vector in the line segment `[g, g']`. -/
def IsShortestIn (g g' g'' : X) : Prop :=
  g'' ∈ segment ℝ g g' ∧ ∀ v ∈ segment ℝ g g', ‖g''‖ ≤ ‖v‖

/-- The shortest vector in `[g, g']` in closed form: `g + τ (g' - g)` with
`τ = clamp_{[0,1]} (⟪g, g - g'⟫ / ‖g - g'‖²)` (and `τ = 0` when `g = g'`, since `a / 0 = 0`). -/
noncomputable def short (g g' : X) : X :=
  g + (max 0 (min 1 (⟪g, g - g'⟫ / ‖g - g'‖ ^ 2))) • (g' - g)

/-- Definition 5.4, p. 13: the concave deviation of `h` on the interval `J`, the infimum of the
Lipschitz constants `K` of convex functions `s` on `J` such that `h + s` is convex on `J`
(`= ⊤` when no such `s` exists). -/
noncomputable def concaveDeviation (h : ℝ → ℝ) (J : Set ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ → ℝ) (K : ℝ≥0) (_ : ConvexOn ℝ J s ∧ ConvexOn ℝ J (h + s) ∧ LipschitzOnWith K s J),
    (K : ℝ≥0∞)

/-- (6.1), p. 16: the nonconvexity modulus `Λ(δ)` of `f` on `C`, the supremum over `x, y ∈ C` with
`‖x - y‖ ≤ δ` of the concave deviation of `t ↦ f(x + (t/δ)(y - x))` on `[0, δ]`. -/
noncomputable def nonconvexityModulus (f : X → ℝ) (C : Set X) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (x ∈ C) (y ∈ C) (_ : ‖x - y‖ ≤ δ),
    concaveDeviation (fun t => f (x + (t / δ) • (y - x))) (Icc 0 δ)

/-- Algorithm 3.1, p. 6, without its stopping test: the interval `(l, r)` after `n` bisections of
`[p, q]`, keeping `[l, m]` when `2 h(m) < h(l) + h(r)` and `[m, r]` otherwise. -/
noncomputable def bisect (h : ℝ → ℝ) (p q : ℝ) : ℕ → ℝ × ℝ
  | 0 => (p, q)
  | n + 1 =>
    let l := (bisect h p q n).1
    let r := (bisect h p q n).2
    let m := (l + r) / 2
    if 2 * h m < h l + h r then (l, m) else (m, r)

/-- The point of the `(j+1)`-st evaluation of `h'₊` in Algorithm 3.1: `p`, then the successive
midpoints. -/
noncomputable def evalPt (h : ℝ → ℝ) (p q : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => ((bisect h p q n).1 + (bisect h p q n).2) / 2

/-- Algorithm 3.1 evaluates `h'₊` (given by `h'`) `k` times without terminating: none of the first
`k` evaluations is negative. -/
def NoStopWithin (h h' : ℝ → ℝ) (p q : ℝ) (k : ℕ) : Prop :=
  ∀ j < k, 0 ≤ h' (evalPt h p q j)

/-- `h'` is the (finite) right derivative of `h` at every point of `[p, q)`, computed from values of
`h` on `[t, q]`. -/
def IsRightDerivOn (h h' : ℝ → ℝ) (p q : ℝ) : Prop :=
  ∀ t ∈ Ico p q, HasDerivWithinAt h (h' t) (Icc t q) t

end NonconvexCost.Complexity


