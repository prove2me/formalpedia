-- Prove2me | Definitions.Def_ErrBoundQG_General_Setting
-- name    : ErrBoundQG_General_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:42.845977+00:00
-- url     : https://prove2.me/theorems/69c2a817-cd4d-4a20-86d4-8f21da924649
-- title:
--   §8, pp. 24–31 (and Def. 5.7, p. 19) — h∘c, proximal/limiting/horizon subdifferentials, transversality, 𝒮_t, 𝒢_t, (sub)regularity, prox-regularity, attentive localizations
-- statement:
--   This file fixes the objects of §8 of Drusvyatskiy and Lewis, the composite problem in full generality. Points live in $\mathbb R^n$ and $\mathbb R^m$ with the Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$, and $\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$. A function $f:\mathbb R^k\to\overline{\mathbb R}$ is *closed* when it is lower semicontinuous, and $|f(x)-f(\bar x)|<\epsilon$ is read for finite values only.
--
--   1. **Proximal subdifferential** (Definition 8.1). For $f(\bar x)$ finite, $\partial_p f(\bar x)$ is the set of $v$ for which there are a neighbourhood $\mathcal X$ of $\bar x$ and $r>0$ with
--   $$f(x)\ge f(\bar x)+\langle v,x-\bar x\rangle-\tfrac r2\|x-\bar x\|^2\qquad\text{for all }x\in\mathcal X .$$
--   2. **Limiting subdifferential** $\partial f(\bar x)$: the limits $v$ of $v_i\in\partial_p f(x_i)$ with $(x_i,f(x_i),v_i)\to(\bar x,f(\bar x),v)$. $\bar x$ is *stationary* when $0\in\partial f(\bar x)$.
--   3. **Horizon subdifferential** $\partial^\infty f(\bar x)$: the limits $v$ of $t_iv_i$ with $v_i\in\partial f(x_i)$, $t_i\searrow0$ and $(x_i,f(x_i))\to(\bar x,f(\bar x))$.
--   4. **Transversality** (Definition 8.2). For $c:\mathbb R^n\to\mathbb R^m$ $C^1$-smooth and $h(c(\bar x))$ finite, $c\pitchfork_{\bar x}h$ means
--   $$\partial^\infty h(c(\bar x))\cap\operatorname{Null}(\nabla c(\bar x)^*)=\{0\}.\qquad(8.3)$$
--   With $h=\delta_Q$ (the indicator of a set $Q$: $0$ on $Q$, $+\infty$ off it) one writes $c\pitchfork_{\bar x}Q$.
--   5. **The problem** (8.2): $\varphi(x)=h(c(x))$, its linearization $\varphi(x;y)=h\big(c(x)+\nabla c(x)(y-x)\big)$ and, for $t>0$, $\varphi_t(x;y)=\varphi(x;y)+\frac1{2t}\|x-y\|^2$.
--   6. **Stationary point map and prox-gradient mapping** (p. 25): $\mathcal S_t(x)=\{z:0\in\partial\varphi_t(x;\cdot)(z)\}$ and $\mathcal G_t(x)=t^{-1}(x-\mathcal S_t(x))$, both set-valued.
--   7. **Subregularity** (Definition 5.7). $F:\mathbb R^n\rightrightarrows\mathbb R^m$ is subregular at $(\bar x,\bar y)\in\operatorname{gph}F$ with constant $l>0$ if for some neighbourhood $\mathcal X$ of $\bar x$
--   $$\operatorname{dist}(x;F^{-1}(\bar y))\le l\cdot\operatorname{dist}(\bar y;F(x))\qquad\text{for all }x\in\mathcal X .$$
--   8. **Metric regularity** (Definition 8.3): the same with $\bar y$ replaced by every $y$ in a neighbourhood $\mathcal Y$ of $\bar y$.
--   9. **Prox-regularity** (Definition 8.7). $f$ is prox-regular at $\bar x$ for $\bar v\in\partial f(\bar x)$ if there are neighbourhoods $\mathcal X\ni\bar x$, $\mathcal V\ni\bar v$ and $\epsilon,r>0$ with $f(y)\ge f(x)+\langle v,y-x\rangle-\frac r2\|y-x\|^2$ for all $x,y\in\mathcal X$ with $|f(x)-f(\bar x)|<\epsilon$ and all $v\in\mathcal V\cap\partial f(x)$.
--   10. **Attentive localizations** (Definition 8.10). $W:\mathbb R^n\rightrightarrows\mathbb R^n$ is a $\varphi$-attentive localization of $\partial\varphi$ around $(\bar x,0)$ if, for some neighbourhoods $\mathcal X\ni\bar x$, $\mathcal V\ni0$ and $\epsilon>0$, $v\in\partial\varphi(x)\iff v\in W(x)$ whenever $x\in\mathcal X$, $v\in\mathcal V$, $|\varphi(x)-\varphi(\bar x)|<\epsilon$. It is a $\varphi(\cdot,\cdot)$-attentive localization of $\mathcal S_t$ around $(\bar x,\bar x)$ if $y\in\mathcal S_t(x)\iff y\in W(x)$ whenever $x\in\mathcal X$, $y\in\mathcal Y$ (a neighbourhood of $\bar x$) and $|\varphi(x;y)-\varphi(\bar x)|<\epsilon$; and $W=t^{-1}(I-\widehat W)$ is a $\varphi(\cdot,\cdot)$-attentive localization of $\mathcal G_t$ around $(\bar x,0)$ when $\widehat W$ is one of $\mathcal S_t$.
--
--   Also defined: the affine perturbation $(G+H)(x)=G(x)+Ax+b$ of a set-valued map by $H(x)=Ax+b$ (Theorem 8.4), "$\nabla c$ is Lipschitz around $\bar x$", and convexity of an extended-real-valued function.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)` and $\overline{\mathbb R}$ is `EReal`; $|a-b|<\epsilon$ for extended reals is `ENear a b ε`, which demands both values finite. The subdifferentials are empty where $f$ is not finite. $\nabla c(x)$ is `fderiv ℝ c x` and $\nabla c(x)^*$ its `ContinuousLinearMap.adjoint`. In (sub)regularity, $\operatorname{dist}(\bar y;F(x))$ is $+\infty$ when $F(x)=\varnothing$, so the inequality is stated for every $v\in F(x)$ with $\|\bar y-v\|$ on the right; in metric regularity the left side must then be finite, so $F^{-1}(y)\neq\varnothing$ is part of the definition (`Metric.infDist` to $\varnothing$ would be $0$). $t_i\searrow0$ is positive, nonincreasing and tending to $0$. The page's "neighbourhood $\mathcal Y$ of $0$" in Definition 8.10 (2) is a neighbourhood of $\bar x$, since the localization is around $(\bar x,\bar x)$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 24–31, (8.2), Definitions 8.1, 8.2 (8.3), 8.3, 8.7, 8.10, 𝒮_t and 𝒢_t on p. 25; p. 19, Definition 5.7

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

namespace ErrBoundQG.General

open scoped InnerProductSpace
open Filter Topology

/-- `f(x)` is finite: neither `+∞` nor `-∞`. -/
def IsFiniteAt {k : ℕ} (f : ErrBoundQG.ProxLin.En k → EReal) (x : ErrBoundQG.ProxLin.En k) : Prop :=
  f x ≠ ⊤ ∧ f x ≠ ⊥

/-- `|a - b| < ε` for extended reals, read as on the page: both values are finite and their real
difference is smaller than `ε` (an infinite value is never `ε`-close to anything). -/
def ENear (a b : EReal) (ε : ℝ) : Prop :=
  a ≠ ⊤ ∧ a ≠ ⊥ ∧ b ≠ ⊤ ∧ b ≠ ⊥ ∧ |a.toReal - b.toReal| < ε

/-- Definition 8.1 (1), p. 25: the proximal subdifferential `∂_p f(x̄)`; empty when `f(x̄)` is
not finite. -/
def proxSubdiff {k : ℕ} (f : ErrBoundQG.ProxLin.En k → EReal) (xbar : ErrBoundQG.ProxLin.En k) : Set (ErrBoundQG.ProxLin.En k) :=
  {v | IsFiniteAt f xbar ∧ ∃ X ∈ 𝓝 xbar, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ X,
    f xbar + ((⟪v, x - xbar⟫_ℝ - r / 2 * ‖x - xbar‖ ^ 2 : ℝ) : EReal) ≤ f x}

/-- Definition 8.1 (2), p. 25: the limiting subdifferential `∂f(x̄)`: limits of proximal
subgradients `vᵢ ∈ ∂_p f(xᵢ)` with `(xᵢ, f(xᵢ), vᵢ) → (x̄, f(x̄), v)`. -/
def limSubdiff {k : ℕ} (f : ErrBoundQG.ProxLin.En k → EReal) (xbar : ErrBoundQG.ProxLin.En k) : Set (ErrBoundQG.ProxLin.En k) :=
  {v | IsFiniteAt f xbar ∧ ∃ xs vs : ℕ → ErrBoundQG.ProxLin.En k, (∀ i, vs i ∈ proxSubdiff f (xs i)) ∧
    Tendsto xs atTop (𝓝 xbar) ∧ Tendsto (fun i => f (xs i)) atTop (𝓝 (f xbar)) ∧
    Tendsto vs atTop (𝓝 v)}

/-- Definition 8.1 (3), p. 25: the horizon subdifferential `∂^∞f(x̄)`: limits of `tᵢvᵢ` with
`vᵢ ∈ ∂f(xᵢ)`, `tᵢ ↘ 0` (positive, nonincreasing, tending to `0`) and
`(xᵢ, f(xᵢ)) → (x̄, f(x̄))`. -/
def horizonSubdiff {k : ℕ} (f : ErrBoundQG.ProxLin.En k → EReal) (xbar : ErrBoundQG.ProxLin.En k) : Set (ErrBoundQG.ProxLin.En k) :=
  {v | IsFiniteAt f xbar ∧ ∃ (xs vs : ℕ → ErrBoundQG.ProxLin.En k) (ts : ℕ → ℝ),
    (∀ i, vs i ∈ limSubdiff f (xs i)) ∧ (∀ i, 0 < ts i) ∧ Antitone ts ∧
    Tendsto ts atTop (𝓝 0) ∧ Tendsto xs atTop (𝓝 xbar) ∧
    Tendsto (fun i => f (xs i)) atTop (𝓝 (f xbar)) ∧
    Tendsto (fun i => ts i • vs i) atTop (𝓝 v)}

/-- The indicator function `δ_Q` of a set `Q`: `0` on `Q`, `+∞` off `Q`. -/
noncomputable def indicatorFun {k : ℕ} (Q : Set (ErrBoundQG.ProxLin.En k)) : ErrBoundQG.ProxLin.En k → EReal :=
  fun y => by classical exact if y ∈ Q then 0 else ⊤

/-- Definition 8.2, p. 25: `c` is transverse to `h` at `x̄` (`c ⋔_x̄ h`): `h(c(x̄))` is finite and
`∂^∞h(c(x̄)) ∩ Null(∇c(x̄)*) = {0}` (8.3). -/
def Transverse {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (h : ErrBoundQG.ProxLin.En m → EReal) (xbar : ErrBoundQG.ProxLin.En n) : Prop :=
  IsFiniteAt h (c xbar) ∧
    horizonSubdiff h (c xbar) ∩ {w | ContinuousLinearMap.adjoint (fderiv ℝ c xbar) w = 0} = {0}

/-- Definition 8.2, p. 25: `c` is transverse to the set `Q` at `x̄` (`c ⋔_x̄ Q`). -/
def TransverseSet {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (Q : Set (ErrBoundQG.ProxLin.En m)) (xbar : ErrBoundQG.ProxLin.En n) : Prop :=
  Transverse c (indicatorFun Q) xbar

/-- The composite objective (8.2), `φ(x) = h(c(x))`. -/
def phi {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (x : ErrBoundQG.ProxLin.En n) : EReal :=
  h (c x)

/-- §8, p. 24 (with `g = 0`): the linearized function `φ(x; y) = h(c(x) + ∇c(x)(y − x))`. -/
noncomputable def phiLin {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (x y : ErrBoundQG.ProxLin.En n) : EReal :=
  h (c x + fderiv ℝ c x (y - x))

/-- §8, p. 24: the quadratic perturbation `φ_t(x; y) = φ(x; y) + ‖x − y‖² / (2t)`. -/
noncomputable def phiT {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (t : ℝ) (x y : ErrBoundQG.ProxLin.En n) :
    EReal :=
  phiLin h c x y + ((‖x - y‖ ^ 2 / (2 * t) : ℝ) : EReal)

/-- p. 25: the stationary point map `𝒮_t(x)`, the stationary points `z` of `φ_t(x; ·)`
(`0 ∈ ∂φ_t(x; ·)(z)`). -/
def statMap {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (t : ℝ) (x : ErrBoundQG.ProxLin.En n) : Set (ErrBoundQG.ProxLin.En n) :=
  {z | 0 ∈ limSubdiff (phiT h c t x) z}

/-- p. 25: the prox-gradient mapping `𝒢_t(x) = t⁻¹(x − 𝒮_t(x))`. -/
def gradMap {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (t : ℝ) (x : ErrBoundQG.ProxLin.En n) : Set (ErrBoundQG.ProxLin.En n) :=
  {u | ∃ z ∈ statMap h c t x, u = t⁻¹ • (x - z)}

/-- The inverse `F⁻¹(y) = {x | y ∈ F(x)}` of a set-valued mapping. -/
def setInv {n m : ℕ} (F : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En m)) (y : ErrBoundQG.ProxLin.En m) : Set (ErrBoundQG.ProxLin.En n) :=
  {x | y ∈ F x}

/-- Definition 5.7, p. 19: `F` is (metrically) subregular at `(x̄, ȳ) ∈ gph F` with constant
`l > 0`: `dist(x; F⁻¹(ȳ)) ≤ l · dist(ȳ; F(x))` for `x` near `x̄`. The universal form over
`v ∈ F(x)` reads `dist(ȳ; ∅) = +∞`. -/
def IsMetricSubregularAt {n m : ℕ} (F : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En m)) (xbar : ErrBoundQG.ProxLin.En n) (ybar : ErrBoundQG.ProxLin.En m) (l : ℝ) :
    Prop :=
  ybar ∈ F xbar ∧ 0 < l ∧
    ∃ X ∈ 𝓝 xbar, ∀ x ∈ X, ∀ v ∈ F x, Metric.infDist x (setInv F ybar) ≤ l * ‖ybar - v‖

/-- Definition 8.3, p. 26: `F` is metrically regular around `(x̄, ȳ) ∈ gph F` with constant
`l > 0`: `dist(x; F⁻¹(y)) ≤ l · dist(y; F(x))` for `x` near `x̄` and `y` near `ȳ`. Whenever
`F(x)` is nonempty the left side must be finite, i.e. `F⁻¹(y)` nonempty (`dist(x; ∅) = +∞`). -/
def IsMetricRegularAround {n m : ℕ} (F : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En m)) (xbar : ErrBoundQG.ProxLin.En n) (ybar : ErrBoundQG.ProxLin.En m) (l : ℝ) :
    Prop :=
  ybar ∈ F xbar ∧ 0 < l ∧
    ∃ X ∈ 𝓝 xbar, ∃ Y ∈ 𝓝 ybar, ∀ x ∈ X, ∀ y ∈ Y, ∀ v ∈ F x,
      (setInv F y).Nonempty ∧ Metric.infDist x (setInv F y) ≤ l * ‖y - v‖

/-- Theorem 8.4, p. 26: the sum `(G + H)(x) = G(x) + H(x)` of a set-valued mapping `G` and the
affine mapping `H(x) = A x + b` (whose derivative is `∇H = A`). -/
def affPert {n m : ℕ} (G : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En m)) (A : ErrBoundQG.ProxLin.En n →L[ℝ] ErrBoundQG.ProxLin.En m) (b : ErrBoundQG.ProxLin.En m) (x : ErrBoundQG.ProxLin.En n) :
    Set (ErrBoundQG.ProxLin.En m) :=
  (fun w => w + (A x + b)) '' G x

/-- Definition 8.7, p. 28: `f` is prox-regular at `x̄` for `v̄ ∈ ∂f(x̄)`. -/
def ProxRegularAt {k : ℕ} (f : ErrBoundQG.ProxLin.En k → EReal) (xbar vbar : ErrBoundQG.ProxLin.En k) : Prop :=
  vbar ∈ limSubdiff f xbar ∧
    ∃ X ∈ 𝓝 xbar, ∃ V ∈ 𝓝 vbar, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ x ∈ X, ∀ y ∈ X, ENear (f x) (f xbar) ε → ∀ v ∈ V ∩ limSubdiff f x,
        f x + ((⟪v, y - x⟫_ℝ - r / 2 * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y

/-- "∇c is (locally) Lipschitz around `x̄`": `‖∇c(x) − ∇c(y)‖ ≤ β‖x − y‖` on a neighbourhood
of `x̄` (operator norm). -/
def JacLipAround {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (xbar : ErrBoundQG.ProxLin.En n) : Prop :=
  ∃ U ∈ 𝓝 xbar, ∃ β : ℝ, ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖

/-- Convexity of an extended-real-valued `h` (never `-∞` where used):
`h((1 − s)y + sz) ≤ (1 − s)h(y) + s h(z)` for `0 < s < 1`. -/
def IsConvexE {k : ℕ} (h : ErrBoundQG.ProxLin.En k → EReal) : Prop :=
  ∀ (y z : ErrBoundQG.ProxLin.En k) (s : ℝ), 0 < s → s < 1 →
    h ((1 - s) • y + s • z) ≤ ((1 - s : ℝ) : EReal) * h y + ((s : ℝ) : EReal) * h z

/-- Definition 8.10 (1), p. 31: `W` is a `φ`-attentive localization of `∂φ` around `(x̄, 0)`. -/
def IsAttentiveLocSubdiff {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (xbar : ErrBoundQG.ProxLin.En n)
    (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) : Prop :=
  ∃ X ∈ 𝓝 xbar, ∃ V ∈ 𝓝 (0 : ErrBoundQG.ProxLin.En n), ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ X, ∀ v ∈ V, ENear (phi h c x) (phi h c xbar) ε →
      (v ∈ limSubdiff (phi h c) x ↔ v ∈ W x)

/-- Definition 8.10 (2), p. 31: `W` is a `φ(·,·)`-attentive localization of `𝒮_t` around
`(x̄, x̄)`. The neighbourhood `𝒴` is a neighbourhood of `x̄` (the page's "𝒴 of 0" is a slip:
the localization is around `(x̄, x̄)`). -/
def IsAttentiveLocStat {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (t : ℝ) (xbar : ErrBoundQG.ProxLin.En n)
    (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) : Prop :=
  ∃ X ∈ 𝓝 xbar, ∃ Y ∈ 𝓝 xbar, ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ X, ∀ y ∈ Y, ENear (phiLin h c x y) (phi h c xbar) ε →
      (y ∈ statMap h c t x ↔ y ∈ W x)

/-- Definition 8.10 (3), p. 31: `W` is a `φ(·,·)`-attentive localization of `𝒢_t` around
`(x̄, 0)`: `W(x) = t⁻¹(x − Ŵ(x))` for a `φ(·,·)`-attentive localization `Ŵ` of `𝒮_t`. -/
def IsAttentiveLocGrad {n m : ℕ} (h : ErrBoundQG.ProxLin.En m → EReal) (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (t : ℝ) (xbar : ErrBoundQG.ProxLin.En n)
    (W : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n)) : Prop :=
  ∃ What : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En n), IsAttentiveLocStat h c t xbar What ∧
    ∀ x, W x = {u | ∃ z ∈ What x, u = t⁻¹ • (x - z)}

end ErrBoundQG.General


