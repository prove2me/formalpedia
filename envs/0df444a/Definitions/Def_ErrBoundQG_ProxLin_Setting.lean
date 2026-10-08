-- Prove2me | Definitions.Def_ErrBoundQG_ProxLin_Setting
-- name    : ErrBoundQG_ProxLin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:01.112137+00:00
-- url     : https://prove2.me/theorems/e4bb8885-a8e7-47d9-85ba-9834e3cdf19b
-- title:
--   §5, pp. 13–14 and Definition 5.7, p. 19 — convex-composite objective, prox-linear map, stationarity, and subregularity
-- statement:
--   Let $g:\mathbb R^n\to\overline{\mathbb R}$ be proper, closed, and convex, let $h:\mathbb R^m\to\mathbb R$ be finite-valued and convex, and let $c:\mathbb R^n\to\mathbb R^m$ be continuously differentiable. The convex-composite objective and its linearization at $x$ are
--
--   $$
--   \varphi(x)=g(x)+h(c(x)),\qquad
--   \varphi(x;y)=g(y)+h(c(x)+\nabla c(x)(y-x)).
--   $$
--
--   For $t>0$, the prox-linear point $x^t$ minimizes $\varphi(x;y)+\|x-y\|^2/(2t)$ over $y$, and the prox-gradient is $\mathcal G_t(x)=t^{-1}(x-x^t)$. The paper defines $\partial\varphi(x)=\partial g(x)+\nabla c(x)^*\partial h(c(x))$ and calls $x$ stationary when this set contains zero.
--
--   A set-valued map $F$ is subregular at $(\bar x,\bar y)$ with constant $l>0$ if $(\bar x,\bar y)$ lies in its graph and, throughout some neighborhood of $\bar x$, $\operatorname{dist}(x,F^{-1}(\bar y))\le l\operatorname{dist}(\bar y,F(x))$. These definitions provide the common notation for the section's comparison theorems.
--
--   **Formalization Note** The prox-linear point is an argmin predicate. The map $\mathcal G_t$ is set-valued, with one value for each argmin; proper closed convex $g$ and $t>0$ ensure a unique argmin. Distance to an empty image of $F$ is interpreted as $+\infty$: the inequality is required for every point $v\in F(x)$, which is equivalent to the distance inequality since $l>0$ and is vacuous when $F(x)=\emptyset$. The definitions accept arbitrary data $g,h,c,t$; the section's standing assumptions (proper closed convex $g$, finite convex $h$, $C^1$-smooth $c$, $t>0$) are hypotheses of each theorem that uses them. The paper's transpose $\nabla c(x)^T$ is the adjoint of the Fréchet derivative.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 13–14, (5.1), §5 prox-linear definitions; p. 19, Definition 5.7

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex

namespace ErrBoundQG.ProxLin

open scoped InnerProductSpace
open Filter

abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The convex-composite objective (5.1). -/
noncomputable def phi {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (x : En n) : EReal :=
  g x + ((h (c x) : ℝ) : EReal)

/-- The linearized objective in §5. -/
noncomputable def phiLin {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (x y : En n) : EReal :=
  g y + ((h (c x + fderiv ℝ c x (y - x)) : ℝ) : EReal)

/-- The quadratically regularized linearization in §5. -/
noncomputable def phiT {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (t : ℝ) (x y : En n) : EReal :=
  phiLin g h c x y + ((‖x - y‖ ^ 2 / (2 * t) : ℝ) : EReal)

/-- A minimizer of the prox-linear subproblem. -/
def IsProxLinPoint {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (t : ℝ) (x p : En n) : Prop :=
  ∀ y, phiT g h c t x p ≤ phiT g h c t x y

/-- The paper's first-order subdifferential for the composite objective. -/
def subdiffPhi {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (x : En n) : Set (En n) :=
  {u | ∃ z ∈ ProxAlg.FixedPoint.subdifferential g x,
       ∃ w ∈ ProxAlg.FixedPoint.subdifferential
         (fun y : En m => ((h y : ℝ) : EReal)) (c x),
         u = z + ContinuousLinearMap.adjoint (fderiv ℝ c x) w}

/-- Stationarity is zero in the paper's composite subdifferential. -/
def IsStationary {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (x : En n) : Prop :=
  0 ∈ subdiffPhi g h c x

/-- The prox-gradient map, represented as a set to preserve its argmin meaning. -/
def proxGradMap {n m : ℕ} (g : En n → EReal) (h : En m → ℝ)
    (c : En n → En m) (t : ℝ) (x : En n) : Set (En n) :=
  {u | ∃ p, IsProxLinPoint g h c t x p ∧ u = t⁻¹ • (x - p)}

/-- Definition 5.7. The universal form treats distance to an empty image as +∞. -/
def IsSubregularAt {n m : ℕ} (F : En n → Set (En m))
    (xbar : En n) (ybar : En m) (l : ℝ) : Prop :=
  ybar ∈ F xbar ∧ 0 < l ∧
    ∃ X ∈ nhds xbar, ∀ x ∈ X, ∀ v ∈ F x,
      Metric.infDist x {z | ybar ∈ F z} ≤ l * ‖ybar - v‖

end ErrBoundQG.ProxLin


