-- Prove2me | Definitions.Def_TaoAnDCA_GlobalOpt_Setting
-- name    : TaoAnDCA_GlobalOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:14.921009+00:00
-- url     : https://prove2.me/theorems/114296e0-bf3b-4532-bd10-bec733bb40db
-- title:
--   §3, pp. 481–483 — dom, the d.c. difference with +∞ − (+∞) = +∞, ∂ and ∂_ε, the standing assumptions (3), the d.c. program (P), its dual (D) and their solution sets
-- statement:
--   Let $X=\mathbb R^n$ with its canonical inner product $\langle\cdot,\cdot\rangle$; the dual space $Y$ is identified with $X$. Functions take values in $\mathbb R\cup\{\pm\infty\}$. Write $\Gamma_0(X)$ for the proper, lower semicontinuous, convex functions $X\to\mathbb R\cup\{+\infty\}$, and $\theta^*(y)=\sup_{x\in X}\{\langle x,y\rangle-\theta(x)\}$ for the conjugate. This file introduces the objects of §3 of Pham Dinh and Le Thi.
--
--   1. The **effective domain** $\operatorname{dom}\theta=\{x\in X:\theta(x)<+\infty\}$.
--   2. The **d.c. difference** $(g-h)(x)=g(x)-h(x)$ under the paper's convention $+\infty-(+\infty)=+\infty$: its value is $+\infty$ whenever $g(x)=+\infty$, and the ordinary extended-real difference otherwise.
--   3. The **exact subdifferential** $\partial\theta(x)$: the set of $y$ such that $\theta(x)<+\infty$ and $\theta(x)+\langle y,z-x\rangle\le\theta(z)$ for all $z\in X$.
--   4. For $\varepsilon\in\mathbb R$ and $x_0\in X$, the **$\varepsilon$-subdifferential**
--   $$\partial_\varepsilon\theta(x_0)=\{y\in Y:\ \theta(x_0)<+\infty\ \text{and}\ \theta(x)\ge\theta(x_0)+\langle x-x_0,y\rangle-\varepsilon\ \ \forall x\in X\}.$$
--   It is empty when $x_0\notin\operatorname{dom}\theta$, in line with the paper, which defines it only for $x_0\in\operatorname{dom}\theta$.
--   5. The **standing assumptions** on a pair $(g,h)$: $g,h\in\Gamma_0(X)$ and the inclusions (3),
--   $$\operatorname{dom}g\subset\operatorname{dom}h,\qquad \operatorname{dom}h^*\subset\operatorname{dom}g^*,$$
--   which the paper assumes throughout.
--   6. The optimal value of the **d.c. program** (P), $\alpha=\inf\{g(x)-h(x):x\in X\}$, its solution set $\mathcal P=\{x: (g-h)(x)\le(g-h)(z)\ \forall z\}$, and the solution set $\mathcal D$ of the **dual program** (D) $\inf\{h^*(y)-g^*(y):y\in Y\}$, with the same convention for $h^*-g^*$.
--
--   These are the objects in which the global optimality condition of Theorem 3.1 and the d.c. duality are stated.
--
--   **Formalization Note** $\Gamma_0(X)$ is the published predicate `ThreeOpSplitting.ConvexRates.IsProperClosedConvex` (never $-\infty$, finite somewhere, lower semicontinuous, convex epigraph), $\partial$ is the published `InertialFB.IFB.IsSubgradient`, and the conjugate is the published `CondatPD.FinDim.conj`, an extended-real supremum over all of $X$ (points with $\theta=+\infty$ contribute $-\infty$). Mathlib's extended-real subtraction has $\top-\top=\bot$, so the paper's $g-h$ and $h^*-g^*$ are written with the explicit difference `dcSub`. Under (3), $h(x)$ is finite whenever $g(x)$ is, so `dcSub` agrees with the real difference on $\operatorname{dom} g$. The solution sets are defined as the sets of minimizers of these extended-real objectives. The paper defines $\partial_\varepsilon$ for $\varepsilon>0$; the Lean definition accepts any real $\varepsilon$, and every statement using it quantifies over $\varepsilon>0$ only.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), pp. 481–483, §3: definitions of g*, dom g, ∂_εg(x°), the convention +∞ − (+∞) = +∞, (P), (D), (3), and the solution sets 𝒫, 𝒟 (p. 483)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

open Filter Topology

namespace TaoAnDCA.GlobalOpt

/-- `dom θ = {x ∈ X : θ(x) < +∞}` (p. 481). -/
def effDom {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | θ x ≠ ⊤}

/-- The d.c. difference `(g − h)(x)` under the paper's convention `+∞ − (+∞) = +∞` (p. 481). -/
noncomputable def dcSub {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  if g x = ⊤ then ⊤ else g x - h x

/-- The exact subdifferential `∂θ(x)` as a set (p. 481), through the published predicate. -/
def subdiff {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | InertialFB.IFB.IsSubgradient θ x y}

/-- The `ε`-subdifferential `∂_ε θ(x₀)` (p. 481), defined for `x₀ ∈ dom θ`. -/
def epsSubdiff {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (ε : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | θ x₀ ≠ ⊤ ∧ ∀ x, θ x₀ + ((inner ℝ (x - x₀) y - ε : ℝ) : EReal) ≤ θ x}

/-- Standing assumptions: `g, h ∈ Γ₀(X)` (p. 481) and the inclusions (3) (p. 482). -/
structure DCStanding {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Prop where
  g_mem : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g
  h_mem : ThreeOpSplitting.ConvexRates.IsProperClosedConvex h
  dom_g_sub : effDom g ⊆ effDom h
  dom_conj_h_sub : effDom (CondatPD.FinDim.conj h) ⊆ effDom (CondatPD.FinDim.conj g)

/-- `α = inf {g(x) − h(x) : x ∈ X}`, problem (P) (p. 481). -/
noncomputable def primalValue {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : EReal :=
  ⨅ x, dcSub g h x

/-- The solution set `𝒫` of (P). -/
def primalSol {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ z, dcSub g h x ≤ dcSub g h z}

/-- The solution set `𝒟` of (D) `inf {h*(y) − g*(y) : y ∈ Y}` (p. 482). -/
def dualSol {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ z, dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y ≤
    dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) z}

end TaoAnDCA.GlobalOpt


