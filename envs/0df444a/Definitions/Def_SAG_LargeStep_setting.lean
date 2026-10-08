-- Prove2me | Definitions.Def_SAG_LargeStep_setting
-- name    : SAG_LargeStep_setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:20.897448+00:00
-- url     : https://prove2.me/theorems/97e17274-11cc-4467-b3f4-d134e8082b9d
-- title:
--   Standing assumptions of the SAG analysis (§3, §A.1) and the gradient variance σ² at the optimum
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be the losses of a finite training set, with average
--   $$g(x)=\frac1n\sum_{i=1}^n f_i(x).$$
--   The **standing assumptions** of the paper's analysis, with constants $L>0$ and $\mu>0$ and a point $x^*\in\mathbb R^p$, are:
--
--   1. each $f_i$ is differentiable, with gradient $f_i'(x)$ at every $x$;
--   2. each $f_i$ is convex;
--   3. each gradient is $L$-Lipschitz: $\|f_i'(x)-f_i'(y)\|\le L\|x-y\|$ for all $x,y$;
--   4. $g$ is $\mu$-strongly convex in the sense that $x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex;
--   5. $x^*$ is a minimizer of $g$ (by strong convexity it is the unique one).
--
--   The **variance of the gradients at the optimum** is
--   $$\sigma^2=\frac1n\sum_{i=1}^n\|f_i'(x^*)\|^2 .$$
--
--   Every theorem of the mission assumes these hypotheses; they are the paper's assumptions of §3 together with the convexity of each $f_i$ stated in §A.1 and used through co-coercivity.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`, the components are indexed by `Fin n` (the paper's $1,\dots,n$, shifted to start at $0$), $g$ is the published `SAGA.Convex.fAvg`, and the gradients are supplied as maps `f' i` tied to `f i` by `HasGradientAt` at every point.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 5, §3 (assumptions, σ²); p. 13, §A.1

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

namespace SAG.LargeStep

/-- The standing assumptions of Le Roux–Schmidt–Bach (arXiv:1202.6258v4, p. 5 §3 and p. 13 §A.1)
for the finite sum `g = (1/n) ∑ᵢ fᵢ` on `ℝᵖ = EuclideanSpace ℝ (Fin p)`, with component indices
`Fin n` (the paper's `1, …, n`):
* `n ≥ 1`, `L > 0`, `μ > 0`;
* each `fᵢ` is differentiable with gradient `f' i` (`HasGradientAt` at every point);
* each `fᵢ` is convex (§A.1);
* each gradient `f' i` is `L`-Lipschitz;
* `g` is `μ`-strongly convex in the paper's sense: `x ↦ g(x) − μ/2‖x‖²` is convex;
* `xstar` minimizes `g`. -/
structure Assumptions {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) : Prop where
  n_pos : 0 < n
  L_pos : 0 < L
  μ_pos : 0 < μ
  hasGradient : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin p)), HasGradientAt (f i) (f' i x) x
  convex : ∀ i : Fin n, ConvexOn ℝ Set.univ (f i)
  lipschitz : ∀ (i : Fin n) (x y : EuclideanSpace ℝ (Fin p)), ‖f' i x - f' i y‖ ≤ L * ‖x - y‖
  strongConvex : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2)
  minimizer : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x

/-- The variance of the gradients at the optimum, `σ² = (1/n) ∑ᵢ ‖f'ᵢ(x*)‖²` (p. 5; p. 14). -/
noncomputable def sigmaSq {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2

end SAG.LargeStep


