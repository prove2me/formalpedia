-- Prove2me | Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
-- name    : GenNewtonSubgrad_ProxReg_VarAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:59.159599+00:00
-- url     : https://prove2.me/theorems/81bb9d4d-0608-4c7e-b2c1-71a7cca8d131
-- title:
--   §2, §4, §5 — normal cones, coderivatives, $\partial^2\varphi$, metric regularity, semismooth*, (H1)–(H3), $C^{1,1}$, Q-superlinear rate, prox-regularity
-- statement:
--   This file fixes the variational-analysis vocabulary of Khanh, Mordukhovich and Phat. Throughout, $E$ and $F$ are real inner product spaces (the paper's $\mathbb R^n$, $\mathbb R^m$), and $E\times F$ carries the pairing $\langle (a_1,a_2),(z_1,z_2)\rangle = \langle a_1,z_1\rangle + \langle a_2,z_2\rangle$.
--
--   1. **Regular normal cone** (2.2). For $\Omega\subseteq E\times F$ and $\bar z\in\Omega$, $a\in\widehat N_\Omega(\bar z)$ iff $\limsup_{z\to_\Omega \bar z}\langle a, z-\bar z\rangle/\|z-\bar z\|\le 0$, i.e. for every $\varepsilon>0$, $\langle a,z-\bar z\rangle\le\varepsilon\|z-\bar z\|$ for all $z\in\Omega$ near $\bar z$. It is empty at points outside $\Omega$.
--   2. **Limiting normal cone** (2.4). $a\in N_\Omega(\bar z)$ iff $\bar z\in\Omega$ and there are $z_k\in\Omega$, $z_k\to\bar z$, and $a_k\to a$ with $a_k\in\widehat N_\Omega(z_k)$.
--   3. **Directional limiting normal cone** (5.1). $a\in N_\Omega(\bar z; d)$ iff $\bar z\in\Omega$ and there are $t_k\downarrow 0$, $d_k\to d$, $a_k\to a$ with $a_k\in\widehat N_\Omega(\bar z+t_kd_k)$.
--   4. **Coderivatives** (2.7) and (p. 16). For a set-valued $G:E\rightrightarrows F$ with graph $\operatorname{gph}G$, $D^*G(\bar x,\bar y)(w)=\{u : (u,-w)\in N_{\operatorname{gph}G}(\bar x,\bar y)\}$ and $D^*G((\bar x,\bar y);(u,v))(w)=\{u^* : (u^*,-w)\in N_{\operatorname{gph}G}((\bar x,\bar y);(u,v))\}$. A single-valued $f$ is identified with $x\mapsto\{f(x)\}$, and $D^*f(\bar x)=D^*f(\bar x,f(\bar x))$.
--   5. **Second-order subdifferential** (2.12). For $\varphi:E\to\overline{\mathbb R}$, $\partial^2\varphi(x,v)(u)=(D^*\partial\varphi)(x,v)(u)$, where $\partial\varphi$ is the limiting subdifferential.
--   6. **Metric regularity** (Definition 2.1(i)). $G$ is metrically regular around $(\bar x,\bar y)\in\operatorname{gph}G$ with modulus $\mu>0$ if there are neighbourhoods $U$ of $\bar x$ and $V$ of $\bar y$ with
--   $$\operatorname{dist}(x;G^{-1}(y))\le\mu\,\operatorname{dist}(y;G(x))\qquad\text{for all }(x,y)\in U\times V,$$
--   where $\operatorname{dist}(\cdot;\emptyset)=+\infty$.
--   7. **Semismooth*** (Definition 5.1). $G$ is semismooth* at $(\bar x,\bar y)\in\operatorname{gph}G$ if $\langle u^*,u\rangle=\langle v^*,v\rangle$ whenever $u^*\in D^*G((\bar x,\bar y);(u,v))(v^*)$, for all directions $(u,v)$.
--   8. **Standing assumptions** (H1)–(H3) (pp. 16–17) on $G:E\rightrightarrows E$ at $(\bar x,\bar v)\in\operatorname{gph}G$: (H1) there are neighbourhoods $U$, $V$ of $\bar x$, $\bar v$ such that for every $(x,v)\in\operatorname{gph}G\cap(U\times V)$ some $d$ satisfies $-v\in D^*G(x,v)(d)$; (H2) $G$ is metrically regular around $(\bar x,\bar v)$; (H3) $G$ is semismooth* at $(\bar x,\bar v)$. With $G=\partial\varphi$, $D^*G(x,v)(d)=\partial^2\varphi(x,v)(d)$ and (H1) is the robust solvability of (3.2).
--   9. **$C^{1,1}$ around $\bar x$**: $\varphi:E\to\mathbb R$ is differentiable on a neighbourhood of $\bar x$ with Lipschitz gradient there.
--   10. **Q-superlinear convergence**: $x^k\to\bar x$ and for every $\varepsilon>0$, $\|x^{k+1}-\bar x\|\le\varepsilon\|x^k-\bar x\|$ for all large $k$.
--   11. **Proper, prox-bounded**: $\varphi:E\to(-\infty,\infty]$ is proper if it never takes $-\infty$ and is finite somewhere; it is prox-bounded if $\varphi(x)\ge -a\|x\|^2-c$ for some reals $a,c$ (p. 27).
--   12. **Prox-regularity** (Definition 4.3). $\varphi$ is prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ and radius $\varepsilon>0$ if $\varphi$ is l.s.c. around $\bar x$ and
--   $$\varphi(x)\ge\varphi(u)+\langle v,x-u\rangle-\frac r2\|x-u\|^2\quad(4.1)$$
--   for all $x,u\in\mathbb B_\varepsilon(\bar x)$ with $|\varphi(u)-\varphi(\bar x)|<\varepsilon$ and all $v\in\partial\varphi(u)\cap\mathbb B_\varepsilon(\bar v)$ (closed balls).
--   13. **Subdifferential continuity** (Definition 4.1): $\varphi(x_k)\to\varphi(\bar x)$ whenever $(x_k,v_k)\to(\bar x,\bar v)$ with $v_k\in\partial\varphi(x_k)$. **Continuous prox-regularity** (p. 14) is the conjunction of 12 and 13.
--
--   These are the objects in which all hypotheses of Theorems 5.7 and 6.6 are expressed.
--
--   **Formalization Note.** The subdifferential $\partial$ is the published analytic limiting subdifferential `NonconvexSplitting.Shared.LimitingSubdiff` (limits of Fréchet subgradients along $\varphi$-attentive sequences), not the paper's geometric (2.9) through epigraph normals; the two coincide for functions l.s.c. around the point, and every function to which $\partial$ is applied in this mission is such a function (prox-regular functions are l.s.c. around $\bar x$; $\langle d,\nabla\varphi\rangle$ is continuous where $\varphi$ is $C^{1,1}$). $E\times F$ carries Mathlib's sup norm; the cones do not depend on which equivalent norm is used. "$t_k\downarrow 0$" in (5.1) is encoded as $t_k>0$, $t_k\to 0$ (equivalent after passing to a subsequence). Metric regularity is encoded so that $G^{-1}(y)$ must be nonempty for $(x,y)\in U\times V$ with $G(x)\neq\emptyset$, matching $\operatorname{dist}(\cdot;\emptyset)=+\infty$. The Q-superlinear rate is stated in $\varepsilon$-form rather than as $\lim\|x^{k+1}-\bar x\|/\|x^k-\bar x\|=0$, because Lean's $0/0=0$ would mishandle iterates equal to $\bar x$. Definition 4.3 as printed says "at a point $x\in\operatorname{dom}\varphi$"; $\bar x$ is meant (and $\bar x\in\operatorname{dom}\varphi$ follows from $\bar v\in\partial\varphi(\bar x)$). The radius $\varepsilon$ of (4.1) is an explicit parameter because Theorem 6.6 names "constants $r,\varepsilon>0$ from (4.1)".
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, pp. 4–7 ((2.2), (2.4), (2.7), Definition 2.1(i), (2.12)), pp. 13–14 (Definitions 4.1, 4.3), pp. 15–17 ((5.1), Definition 5.1, (H1)–(H3), (5.2)), p. 20 (Theorem 5.7), p. 27 (prox-boundedness)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.ProxReg

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The pairing `⟨(a₁, a₂), (z₁, z₂)⟩ = ⟨a₁, z₁⟩ + ⟨a₂, z₂⟩` on `E × F`. -/
def pairInner (a z : E × F) : ℝ :=
  ⟪a.1, z.1⟫_ℝ + ⟪a.2, z.2⟫_ℝ

/-- The regular (Fréchet) normal cone (2.2) to `S ⊆ E × F` at `z`: `z ∈ S` and
`limsup_{w →_S z} ⟨a, w - z⟩ / ‖w - z‖ ≤ 0`. Empty when `z ∉ S`. -/
def regNormal (S : Set (E × F)) (z : E × F) : Set (E × F) :=
  {a | z ∈ S ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 z, w ∈ S → pairInner a (w - z) ≤ ε * ‖w - z‖}

/-- The limiting (Mordukhovich) normal cone (2.4) to `S` at `z ∈ S`. -/
def limNormal (S : Set (E × F)) (z : E × F) : Set (E × F) :=
  {a | z ∈ S ∧ ∃ zs as : ℕ → E × F, (∀ k, zs k ∈ S) ∧ Tendsto zs atTop (𝓝 z) ∧
    Tendsto as atTop (𝓝 a) ∧ ∀ k, as k ∈ regNormal S (zs k)}

/-- The directional limiting normal cone (5.1) to `S` at `z ∈ S` in the direction `d`. -/
def dirLimNormal (S : Set (E × F)) (z d : E × F) : Set (E × F) :=
  {a | z ∈ S ∧ ∃ (ts : ℕ → ℝ) (ds as : ℕ → E × F), (∀ k, 0 < ts k) ∧
    Tendsto ts atTop (𝓝 0) ∧ Tendsto ds atTop (𝓝 d) ∧ Tendsto as atTop (𝓝 a) ∧
    ∀ k, as k ∈ regNormal S (z + ts k • ds k)}

/-- The graph of a set-valued map. -/
def gph (G : E → Set F) : Set (E × F) :=
  {p | p.2 ∈ G p.1}

/-- The limiting coderivative (2.7): `D*G(x, y)(w) = {u | (u, -w) ∈ N_{gph G}(x, y)}`. -/
def coderiv (G : E → Set F) (x : E) (y : F) (w : F) : Set E :=
  {u | (u, -w) ∈ limNormal (gph G) (x, y)}

/-- The directional limiting coderivative `D*G((x, y); (u, v))(w)` (p. 16). -/
def dirCoderiv (G : E → Set F) (x : E) (y : F) (u : E) (v : F) (w : F) : Set E :=
  {u' | (u', -w) ∈ dirLimNormal (gph G) (x, y) (u, v)}

/-- A single-valued map as a set-valued map. -/
def sv (f : E → F) : E → Set F :=
  fun x => {f x}

/-- The second-order subdifferential (2.12): `∂²φ(x, v)(u) = (D*∂φ)(x, v)(u)`. -/
def secondSubdiff (φ : E → EReal) (x v u : E) : Set E :=
  coderiv (NonconvexSplitting.Shared.LimitingSubdiff φ) x v u

/-- Metric regularity of `G` around `(x̄, ȳ)` with modulus `μ` (Definition 2.1(i)), with
`dist(x; ∅) = +∞`: the inverse image `G⁻¹(y)` must be nonempty for `y` near `ȳ`. -/
def IsMetricRegularAround (G : E → Set F) (xbar : E) (ybar : F) (μ : ℝ) : Prop :=
  ybar ∈ G xbar ∧ 0 < μ ∧ ∃ U ∈ 𝓝 xbar, ∃ V ∈ 𝓝 ybar, ∀ x ∈ U, ∀ y ∈ V, ∀ w ∈ G x,
    {x' | y ∈ G x'}.Nonempty ∧ Metric.infDist x {x' | y ∈ G x'} ≤ μ * ‖y - w‖

/-- `G` is metrically regular around `(x̄, ȳ)` with some modulus. -/
def MetricRegularAround (G : E → Set F) (xbar : E) (ybar : F) : Prop :=
  ∃ μ, IsMetricRegularAround G xbar ybar μ

/-- The semismooth* property (Definition 5.1) of `G` at `(x̄, ȳ) ∈ gph G`. -/
def IsSemismoothStar (G : E → Set F) (xbar : E) (ybar : F) : Prop :=
  ybar ∈ G xbar ∧ ∀ (u : E) (v : F) (w : F), ∀ u' ∈ dirCoderiv G xbar ybar u v w,
    ⟪u', u⟫_ℝ = ⟪w, v⟫_ℝ

/-- (H1) with (3.2): the inclusion `-v ∈ D*G(x, v)(d)` is solvable in `d` for every
`(x, v) ∈ gph G` near `(x̄, v̄)`. -/
def H1 (G : E → Set E) (xbar vbar : E) : Prop :=
  ∃ U ∈ 𝓝 xbar, ∃ V ∈ 𝓝 vbar, ∀ x ∈ U, ∀ v ∈ V, v ∈ G x → ∃ d, -v ∈ coderiv G x v d

/-- The standing assumptions (H1)–(H3) on `G` at `(x̄, v̄)`. -/
def StandingH (G : E → Set E) (xbar vbar : E) : Prop :=
  vbar ∈ G xbar ∧ H1 G xbar vbar ∧ MetricRegularAround G xbar vbar ∧ IsSemismoothStar G xbar vbar

/-- `φ` is of class `C^{1,1}` around `x̄`: differentiable on a neighbourhood with Lipschitz
gradient there. -/
def IsC11Around [CompleteSpace E] (φ : E → ℝ) (xbar : E) : Prop :=
  ∃ U ∈ 𝓝 xbar, (∀ x ∈ U, DifferentiableAt ℝ φ x) ∧ ∃ L, LipschitzOnWith L (gradient φ) U

/-- Q-superlinear convergence of `x` to `x̄`, in the ε-form of
`‖x^{k+1} - x̄‖ / ‖x^k - x̄‖ → 0` (no division, so no `0/0`). -/
def IsQSuperlinear (x : ℕ → E) (xbar : E) : Prop :=
  Tendsto x atTop (𝓝 xbar) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k + 1) - xbar‖ ≤ ε * ‖x k - xbar‖

/-- `|a - b| < ε` for finite extended reals `a`, `b`. -/
def ENear (a b : EReal) (ε : ℝ) : Prop :=
  a ≠ ⊤ ∧ a ≠ ⊥ ∧ b ≠ ⊤ ∧ b ≠ ⊥ ∧ |a.toReal - b.toReal| < ε

/-- `φ : E → (-∞, ∞]` is proper. -/
def IsProperFn (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ ∃ x, φ x ≠ ⊤

/-- `φ` is prox-bounded: bounded from below by a quadratic function. -/
def IsProxBounded (φ : E → EReal) : Prop :=
  ∃ a c : ℝ, ∀ x, (((-(a * ‖x‖ ^ 2) - c) : ℝ) : EReal) ≤ φ x

/-- Prox-regularity (Definition 4.3) of `φ` at `x̄` for `v̄ ∈ ∂φ(x̄)` with modulus `r` and
radius `ε` of (4.1). -/
def IsProxRegularAt (φ : E → EReal) (xbar vbar : E) (r ε : ℝ) : Prop :=
  vbar ∈ NonconvexSplitting.Shared.LimitingSubdiff φ xbar ∧ 0 < r ∧ 0 < ε ∧
    (∃ U ∈ 𝓝 xbar, ∀ x ∈ U, LowerSemicontinuousAt φ x) ∧
    ∀ x ∈ Metric.closedBall xbar ε, ∀ u ∈ Metric.closedBall xbar ε, ENear (φ u) (φ xbar) ε →
      ∀ v ∈ NonconvexSplitting.Shared.LimitingSubdiff φ u ∩ Metric.closedBall vbar ε,
        φ u + ((⟪v, x - u⟫_ℝ - r / 2 * ‖x - u‖ ^ 2 : ℝ) : EReal) ≤ φ x

/-- Subdifferential continuity (Definition 4.1) of `φ` at `x̄` for `v̄`. -/
def IsSubdiffContinuousAt (φ : E → EReal) (xbar vbar : E) : Prop :=
  ∀ xs vs : ℕ → E, Tendsto xs atTop (𝓝 xbar) → Tendsto vs atTop (𝓝 vbar) →
    (∀ k, vs k ∈ NonconvexSplitting.Shared.LimitingSubdiff φ (xs k)) →
      Tendsto (fun k => φ (xs k)) atTop (𝓝 (φ xbar))

/-- Continuous prox-regularity: prox-regular and subdifferentially continuous (p. 14). -/
def IsContProxRegularAt (φ : E → EReal) (xbar vbar : E) (r ε : ℝ) : Prop :=
  IsProxRegularAt φ xbar vbar r ε ∧ IsSubdiffContinuousAt φ xbar vbar

end GenNewtonSubgrad.ProxReg


