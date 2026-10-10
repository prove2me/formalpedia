-- Prove2me | Definitions.Def_FullyCoupledSDE_DiffApprox_Setting
-- name    : FullyCoupledSDE_DiffApprox_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:59.896174+00:00
-- url     : https://prove2.me/theorems/669fb4a8-2a3e-4220-8c93-3e8f43152b80
-- title:
--   Notations (p. 1209), (1.2), (1.4), (1.8), (Aσ), (Ab), (AG), (AH), (2.7), (2.9), (4.1) — Hölder classes, L0, μ^y, weak solutions, averaged coefficients
-- statement:
--   This file fixes the objects of Röckner and Xie's diffusion approximation theorem for the fully coupled two-scale system (1.4). Throughout, $x\in\mathbb R^{d_1}$ is the fast variable and $y\in\mathbb R^{d_2}$ the slow one, both with the Euclidean norm $|\cdot|$; time is $t\in\mathbb R_+$.
--
--   **Weighted Hölder classes** (Notations, p. 1209). For $0<\delta\le 1$ and $\vartheta\ge 0$ write $k=[\vartheta]$ and $\theta=\vartheta-k$. A function $g(x,y)$ (vector- or matrix-valued) lies in $C^{\delta,\vartheta}_p$ when there are $C,m>0$ such that
--
--   1. $|g(x,y)|\le C(1+|x|^m)$ (polynomial growth in $x$, uniformly in $y$);
--   2. for every $x$, $y\mapsto g(x,y)$ has $k$ derivatives, and every $\partial_y^j g$ with $j<k$ satisfies the growth bound and
--   $$|h(x_1,y)-h(x_2,y)|\le C(|x_1-x_2|^\delta\wedge 1)(1+|x_1|^m+|x_2|^m);$$
--   3. the top derivative $h=\partial_y^k g$ satisfies the same bound if $\theta=0$, and if $\theta>0$ the joint bound
--   $$|h(x_1,y_1)-h(x_2,y_2)|\le C\big[(|x_1-x_2|^\delta\wedge1)+(|y_1-y_2|^\theta\wedge1)\big](1+|x_1|^m+|x_2|^m).$$
--
--   The bounded class $C^{\delta,\vartheta}_b$ is the same with weight $1$ ($m=0$). For $0<\gamma\le1$, $C^{\gamma,\delta,\vartheta}_p$ consists of time-dependent $f(t,x,y)$ with $f(t,\cdot,\cdot)\in C^{\delta,\vartheta}_p$ and $|f(t,x,y)-f(s,x,y)|\le C|t-s|^\gamma(1+|x|^m)$, all constants uniform in $t$. $L^\infty_p$ is the class of measurable $f$ with $|f(t,x,y)|\le C(1+|x|^m)$. On $\mathbb R^{d_2}$ alone, $C^\eta_b$ asks for bounded derivatives up to order $[\eta]$ (those of lower order differentiable) and a $(\eta-[\eta])$-Hölder top derivative; $C^{\gamma,\eta}_b$ adds $\gamma$-Hölder continuity in time, uniformly.
--
--   **The frozen operator and its invariant family.** With $a=\sigma\sigma^*/2$,
--   $$\mathscr L_0(x,y)u=\sum_{i,j}a^{ij}(x,y)\,\partial^2_{x_ix_j}u+\sum_i b^i(x,y)\,\partial_{x_i}u,$$
--   the generator of the frozen SDE $dX^y_t=b(X^y_t,y)dt+\sigma(X^y_t,y)dW^1_t$ (1.7). The family $(\mu^y)_y$ is a family of probability measures on $\mathbb R^{d_1}$ with $\int\mathscr L_0(\cdot,y)g\,d\mu^y=0$ for every smooth compactly supported $g$. A function $f$ is *centered* (1.3) when $x\mapsto f(x,y)$ is $\mu^y$-integrable with integral $0$ for every $y$ (and every $t$).
--
--   **Assumptions.** (Aσ): $\lambda^{-1}|\xi|^2\le|\sigma\sigma^*(x,y)\xi|^2\le\lambda|\xi|^2$ for some $\lambda>1$. (Ab): $\lim_{|x|\to\infty}\sup_y\langle x,b(x,y)\rangle=-\infty$. (AG): $\lambda^{-1}|\xi|^2\le|GG^*(t,x,y)\xi|^2\le\lambda|\xi|^2$. (2.7): $\lim_{|x|\to\infty}\sup_y\langle x,b(x,y)+\kappa c(x,y)\rangle=-\infty$ for all small $\kappa>0$.
--
--   **The system and the limit.** For parameters $\alpha,\beta,\gamma>0$, a weak solution of
--   $$dX_t=\alpha^{-2}b(X_t,Y_t)dt+\beta^{-1}c(X_t,Y_t)dt+\alpha^{-1}\sigma(X_t,Y_t)dW^1_t,\qquad dY_t=F(t,X_t,Y_t)dt+\gamma^{-1}H(t,X_t,Y_t)dt+G(t,X_t,Y_t)dW^2_t,$$
--   $(X_0,Y_0)=(x,y)$, on $[0,T]$, is a filtered probability space with a Brownian motion $W=(W^1,W^2)$ for the filtration and a progressive process solving (1.4) in the Itô sense. Similarly for the averaged equation (2.9), $d\hat Y_t=\hat F(t,\hat Y_t)dt+\hat G(t,\hat Y_t)dW^2_t$, $\hat Y_0=y$. The averaged coefficients of Regime 1 are $\hat F_1(t,y)=\int F(t,x,y)\mu^y(dx)$, any measurable $\hat G$ with $\hat G\hat G^*=\int GG^*\,d\mu^y$ (a version of $\hat G_1$), and $\hat{\mathcal G}_1=\hat G_1\hat G_1^*/2$.
--
--   **Parameters.** $\alpha_\varepsilon,\beta_\varepsilon,\gamma_\varepsilon>0$ tend to $0$ with $\alpha_\varepsilon^2/\beta_\varepsilon\to0$ (p. 1206); Regime 1 is $\alpha_\varepsilon/\gamma_\varepsilon\to0$ and $\alpha_\varepsilon^2/(\beta_\varepsilon\gamma_\varepsilon)\to0$ (1.8). Finally (4.1) defines the mollification $f_n=f*\rho_2^n*\rho_1^n$ in $(t,y)$ with $\rho^n_1(r)=n^2\rho_1(n^2r)$, $\rho^n_2(z)=n^{d_2}\rho_2(nz)$.
--
--   **Formalization Note.** Spaces are `EuclideanSpace ℝ (Fin d)`; matrices enter the classes through `Matrix.of.symm` (entrywise sup norm, equivalent to any norm). The Itô layer is the published `Peng1990.SMP.Stochastic`. The invariant measures are read analytically (infinitesimal invariance), which under the standing assumptions characterizes the unique invariant measure of (1.7). The Hölder classes constrain all lower $y$-derivatives, include the growth bound, and take their constants uniformly in $t$ (also in the time-Hölder clause); the derivative clauses require differentiability, not continuity, of the top derivative. Time $t=0$ is included in the class conditions. $\sigma$ and $G$ are square ($d_1\times d_1$, $d_2\times d_2$), so $W^1,W^2$ are $d_1$- and $d_2$-dimensional. A solution is an Itô process in the sense of the referenced layer: progressive, with $\sup_{t\le T}\mathbb E|Z_t|^2<\infty$ and diffusion integrands in $L^2(\Omega\times[0,T])$; the moment estimates of the paper's solutions give these properties.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), pp. 1206–1212, 1222, 1229: (1.2), (1.4), (1.7), (1.8), Notations (p. 1209), (Aσ), (AG), (Ab), (AH), (2.7), F̂_1 and Ĝ_1 (p. 1211), (2.9), (4.1), 𝒢̂_k (p. 1229)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ContDiff Matrix

/-! ### Spaces -/

/-! ### Weighted Hölder classes (Notations, p. 1209)

All classes take values in a normed group `F`, so that vectors, matrices (through
`Matrix.of.symm`, entrywise sup norm) and iterated derivatives (continuous multilinear maps)
fit. The weight exponent `m = 0` gives the bounded classes (subscript `b`), since `‖x‖ ^ 0 = 1`. -/

section Classes

variable {d1 d2 : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- Index `δ` in `x`, index `0` in `y`, with constants `C, m`: growth `‖g x y‖ ≤ C(1 + |x|^m)` and
`‖g(x1,y) − g(x2,y)‖ ≤ C(|x1 − x2|^δ ∧ 1)(1 + |x1|^m + |x2|^m)` for every `y`. -/
def HolX0 (δ C m : ℝ) (g : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) : Prop :=
  (∀ x y, ‖g x y‖ ≤ C * (1 + ‖x‖ ^ m)) ∧
  ∀ x1 x2 y, ‖g x1 y - g x2 y‖ ≤ C * min (‖x1 - x2‖ ^ δ) 1 * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m)

/-- Index `δ` in `x`, index `θ ∈ (0,1)` in `y`, with constants `C, m`: growth and
`‖g(x1,y1) − g(x2,y2)‖ ≤ C[(|x1 − x2|^δ ∧ 1) + (|y1 − y2|^θ ∧ 1)](1 + |x1|^m + |x2|^m)`. -/
def HolXY (δ θ C m : ℝ) (g : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) : Prop :=
  (∀ x y, ‖g x y‖ ≤ C * (1 + ‖x‖ ^ m)) ∧
  ∀ x1 x2 y1 y2, ‖g x1 y1 - g x2 y2‖ ≤
    C * (min (‖x1 - x2‖ ^ δ) 1 + min (‖y1 - y2‖ ^ θ) 1) * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m)

/-- The class `C^{δ,ϑ}` (`0 < δ ≤ 1`, `ϑ ≥ 0`) with fixed constants `C, m`. With `k := ⌊ϑ⌋`
and `θ := ϑ − k`: for each `x`, `y ↦ g x y` has `k` derivatives (the derivatives of order
`< k` are differentiable); the derivatives `∂_y^j g` of order `j < k` lie in the index-`(δ, 0)`
class; the top derivative `∂_y^k g` lies in the index-`(δ, 0)` class if `θ = 0` and in the
index-`(δ, θ)` class if `θ > 0`. -/
def HolderCore (δ ϑ C m : ℝ) (g : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  (∀ x, ∀ j < ⌊ϑ⌋₊, Differentiable ℝ (iteratedFDeriv ℝ j (g x))) ∧
  (∀ j < ⌊ϑ⌋₊, HolX0 δ C m (fun x y => iteratedFDeriv ℝ j (g x) y)) ∧
  (ϑ - ⌊ϑ⌋₊ = 0 → HolX0 δ C m (fun x y => iteratedFDeriv ℝ ⌊ϑ⌋₊ (g x) y)) ∧
  (ϑ - ⌊ϑ⌋₊ ≠ 0 → HolXY δ (ϑ - ⌊ϑ⌋₊) C m (fun x y => iteratedFDeriv ℝ ⌊ϑ⌋₊ (g x) y))

/-- `C^{δ,ϑ}_p`: polynomial growth in `x`, uniformly in `y`. -/
def Cp (δ ϑ : ℝ) (g : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  ∃ C > 0, ∃ m > 0, HolderCore δ ϑ C m g

/-- `C^{δ,ϑ}_b`: the bounded class (weight exponent `m = 0`). -/
def Cb (δ ϑ : ℝ) (g : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  ∃ C > 0, HolderCore δ ϑ C 0 g

/-- `C^{γ,δ,ϑ}_p` (`0 < γ ≤ 1`) for a time-dependent `f`, time in a metric space `τ`
(`ℝ≥0`, or `ℝ` for an extension): for every `t`, `f t ∈ C^{δ,ϑ}_p`, and for every `(x, y)`,
`t ↦ f t x y` is `γ`-Hölder and bounded, all with constants `C, m` uniform in `t, x, y`
(the time-Hölder constant carries the weight `1 + |x|^m`). -/
def CpT {τ : Type*} [PseudoMetricSpace τ] (γ δ ϑ : ℝ) (f : τ → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F)
    [NormedSpace ℝ F] : Prop :=
  ∃ C > 0, ∃ m > 0, (∀ t, HolderCore δ ϑ C m (f t)) ∧
    ∀ t s x y, ‖f t x y - f s x y‖ ≤ C * dist t s ^ γ * (1 + ‖x‖ ^ m)

/-- `L^∞_p`: (strongly) measurable in `(t, x, y)` and `‖f(t,x,y)‖ ≤ C(1 + |x|^m)` for `t > 0`. -/
def LpInf (f : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) : Prop :=
  StronglyMeasurable (fun p : ℝ≥0 × FullyCoupledSDE.Poisson.E d1 × FullyCoupledSDE.Poisson.E d2 => f p.1 p.2.1 p.2.2) ∧
  ∃ C > 0, ∃ m > 0, ∀ t : ℝ≥0, 0 < t → ∀ x y, ‖f t x y‖ ≤ C * (1 + ‖x‖ ^ m)

/-- The bounded class `C^η_b(ℝ^{d2})` with constant `C`: with `k := ⌊η⌋`, `θ := η − k`, the
derivatives of order `< k` are differentiable, the derivatives of order `≤ k` are bounded by
`C`, and if `θ > 0` the `k`-th derivative is `θ`-Hölder with constant `C`. -/
def HolYCore (η C : ℝ) (g : FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  (∀ j < ⌊η⌋₊, Differentiable ℝ (iteratedFDeriv ℝ j g)) ∧
  (∀ j ≤ ⌊η⌋₊, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ C) ∧
  (η - ⌊η⌋₊ ≠ 0 → ∀ y1 y2,
    ‖iteratedFDeriv ℝ ⌊η⌋₊ g y1 - iteratedFDeriv ℝ ⌊η⌋₊ g y2‖ ≤ C * ‖y1 - y2‖ ^ (η - ⌊η⌋₊))

/-- `C^η_b(ℝ^{d2})`. -/
def CbY (η : ℝ) (g : FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  ∃ C > 0, HolYCore η C g

/-- `C^{γ,η}_b` on `ℝ₊ × ℝ^{d2}`: `f t ∈ C^η_b` for every `t` and `t ↦ f t y` is bounded and
`γ`-Hölder, with constants uniform in `t, y`. -/
def CbTY (γ η : ℝ) (f : ℝ≥0 → FullyCoupledSDE.Poisson.E d2 → F) [NormedSpace ℝ F] : Prop :=
  ∃ C > 0, (∀ t, HolYCore η C (f t)) ∧ ∀ t s y, ‖f t y - f s y‖ ≤ C * dist t s ^ γ

end Classes

/-! ### The frozen operator, the assumptions, the invariant family -/

section Frozen

variable {d1 d2 : ℕ}

/-- The operator `L0(x,y)` of (1.2) with `a := σσ*/2` (the convention of §1.2, p. 1207), so that
`L0(·,y)` is the generator of the frozen SDE (1.7):
`L0 u(x) = Σ_{ij} a^{ij}(x,y) ∂²_{x_i x_j} u(x,y) + Σ_i b^i(x,y) ∂_{x_i} u(x,y)`. -/
noncomputable def L0 (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (y : FullyCoupledSDE.Poisson.E d2) (u : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ) (x : FullyCoupledSDE.Poisson.E d1) : ℝ :=
  (∑ i, ∑ j, (1 / 2 : ℝ) * (σ x y * (σ x y)ᵀ) i j *
      iteratedFDeriv ℝ 2 (fun x' => u x' y) x ![FullyCoupledSDE.Poisson.e i, FullyCoupledSDE.Poisson.e j]) +
    ∑ i, b x y i * fderiv ℝ (fun x' => u x' y) x (FullyCoupledSDE.Poisson.e i)

/-- (Aσ), p. 1209: `a = σσ*` is nondegenerate in `x` uniformly in `y`:
`λ⁻¹|ξ|² ≤ |a(x,y)ξ|² ≤ λ|ξ|²` for some `λ > 1`. -/
def AssumpSigma (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) : Prop :=
  ∃ lam > (1 : ℝ), ∀ x y (ξ : FullyCoupledSDE.Poisson.E d1),
    lam⁻¹ * ‖ξ‖ ^ 2 ≤ ‖Matrix.toEuclideanLin (σ x y * (σ x y)ᵀ) ξ‖ ^ 2 ∧
    ‖Matrix.toEuclideanLin (σ x y * (σ x y)ᵀ) ξ‖ ^ 2 ≤ lam * ‖ξ‖ ^ 2

/-- (2.7), p. 1211, read with `ε` the factor `α_ε²/β_ε` that multiplies `c` in the drift of
`X^ε`: `lim_{|x|→∞} sup_y ⟨x, b(x,y) + κ c(x,y)⟩ = −∞` for every small enough `κ > 0`. -/
def Assump27 (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1) : Prop :=
  ∃ κ0 > (0 : ℝ), ∀ κ ∈ Set.Ioc (0 : ℝ) κ0, ∀ M : ℝ, ∃ R : ℝ, ∀ x y, R ≤ ‖x‖ →
    inner ℝ x (b x y + κ • c x y) ≤ M

/-- (AG), p. 1209: `𝒢 = GG*` is nondegenerate in `y` uniformly in `(t,x)`. -/
def AssumpG (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ) : Prop :=
  ∃ lam > (1 : ℝ), ∀ t x y (ξ : FullyCoupledSDE.Poisson.E d2),
    lam⁻¹ * ‖ξ‖ ^ 2 ≤ ‖Matrix.toEuclideanLin (G t x y * (G t x y)ᵀ) ξ‖ ^ 2 ∧
    ‖Matrix.toEuclideanLin (G t x y * (G t x y)ᵀ) ξ‖ ^ 2 ≤ lam * ‖ξ‖ ^ 2

/-- `μ = (μ^y)_y` is the invariant family of the frozen SDE (1.7), read analytically: every
`μ^y` is a probability measure, infinitesimally invariant for `L0(·,y)`:
`∫ L0(·,y) g dμ^y = 0` for every smooth compactly supported `g`. -/
def IsInvariantFamily (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) : Prop :=
  (∀ y, IsProbabilityMeasure (μ y)) ∧
  ∀ y (g : FullyCoupledSDE.Poisson.E d1 → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    ∫ x, L0 σ b y (fun x' _ => g x') x ∂(μ y) = 0

/-- The centering condition (1.3): for every `y`, `x ↦ f(x,y)` is `μ^y`-integrable with
integral `0`. -/
def Centered {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (f : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) : Prop :=
  ∀ y, Integrable (fun x => f x y) (μ y) ∧ ∫ x, f x y ∂(μ y) = 0

/-- Centering for a time-dependent `f`, for every `t` (as in (2.6)). -/
def CenteredT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (f : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → F) : Prop :=
  ∀ t, Centered μ (f t)

end Frozen

/-! ### The averaged coefficients for Regime 1 (p. 1211, p. 1229) -/

section Averaged

variable {d1 d2 : ℕ}

/-- `F̂_1(t,y) := ∫ F(t,x,y) μ^y(dx)`. -/
noncomputable def Fhat1 (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (F : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2)
    (t : ℝ≥0) (y : FullyCoupledSDE.Poisson.E d2) : FullyCoupledSDE.Poisson.E d2 :=
  ∫ x, F t x y ∂(μ y)

/-- `𝒢̂_1(t,y) := Ĝ_1Ĝ_1*(t,y)/2 = ½ ∫ GG*(t,x,y) μ^y(dx)` (entrywise), the second-order
coefficient of the generator `L̂_1` of (2.9) (p. 1229). -/
noncomputable def GcalHat1 (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1))
    (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ) (t : ℝ≥0) (y : FullyCoupledSDE.Poisson.E d2) :
    Matrix (Fin d2) (Fin d2) ℝ :=
  Matrix.of fun i j => (1 / 2 : ℝ) * ∫ x, (G t x y * (G t x y)ᵀ) i j ∂(μ y)

/-- `Ĝ` is a version of `Ĝ_1 = √(∫ GG* dμ^y)`: `Ĝ(t,y)Ĝ(t,y)* = ∫ GG*(t,x,y) μ^y(dx)`
entrywise, and `Ĝ` is measurable. -/
def IsGhat1 (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (Ghat : ℝ≥0 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ) : Prop :=
  (∀ i j, Measurable (fun p : ℝ≥0 × FullyCoupledSDE.Poisson.E d2 => Ghat p.1 p.2 i j)) ∧
  ∀ t y i j, (Ghat t y * (Ghat t y)ᵀ) i j = ∫ x, (G t x y * (G t x y)ᵀ) i j ∂(μ y)

end Averaged

/-! ### Brownian motion, the system (1.4) and the limit equation (2.9) -/

section SDE

variable {d1 d2 : ℕ}

/-- A standard `d`-dimensional `𝓕`-Brownian motion: Peng's `IsStdBrownian`, adapted to `𝓕`, with
`W t − W s` independent of `𝓕 s` for `s ≤ t`. -/
def IsFBrownian {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  Peng1990.SMP.IsStdBrownian P W ∧ StronglyAdapted 𝓕 W ∧
  ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun o => W t o - W s o) inferInstance) (𝓕 s) P

/-- The `x`-block `(z_i)_{i ≤ d1}` of a state `z ∈ ℝ^{d1+d2}`, as a point of `ℝ^{d1}`. -/
def xOf (z : Fin d1 ⊕ Fin d2 → ℝ) : FullyCoupledSDE.Poisson.E d1 := WithLp.toLp 2 (fun i => z (Sum.inl i))

/-- The `y`-block of a state `z ∈ ℝ^{d1+d2}`, as a point of `ℝ^{d2}`. -/
def yOf (z : Fin d1 ⊕ Fin d2 → ℝ) : FullyCoupledSDE.Poisson.E d2 := WithLp.toLp 2 (fun i => z (Sum.inr i))

/-- The drift of (1.4) at time `s` and state `z = (x, y)`:
`(α⁻² b(x,y) + β⁻¹ c(x,y), F(s,x,y) + γ⁻¹ H(s,x,y))`. -/
noncomputable def drift14 (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1) (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2)
    (α β γ : ℝ) (s : ℝ≥0) (z : Fin d1 ⊕ Fin d2 → ℝ) : Fin d1 ⊕ Fin d2 → ℝ :=
  Sum.elim (fun i => (α ^ 2)⁻¹ * b (xOf z) (yOf z) i + β⁻¹ * c (xOf z) (yOf z) i)
    (fun i => F s (xOf z) (yOf z) i + γ⁻¹ * H s (xOf z) (yOf z) i)

/-- The `j`-th diffusion column of (1.4), for the `(d1 + d2)`-dimensional Brownian motion
`W = (W¹, W²)` (`W¹` = the first `d1` coordinates, `W²` = the last `d2`):
`dX = … + α⁻¹ σ(X,Y) dW¹`, `dY = … + G(s,X,Y) dW²`. -/
noncomputable def diff14 (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ)
    (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ) (α : ℝ) (j : Fin (d1 + d2))
    (s : ℝ≥0) (z : Fin d1 ⊕ Fin d2 → ℝ) : Fin d1 ⊕ Fin d2 → ℝ :=
  Sum.elim
    (fun i => Sum.elim (fun k => α⁻¹ * σ (xOf z) (yOf z) i k) (fun _ => 0) (finSumFinEquiv.symm j))
    (fun i => Sum.elim (fun _ => 0) (fun k => G s (xOf z) (yOf z) i k) (finSumFinEquiv.symm j))

/-- `(𝓕, P, W, Z)` is a weak solution on `[0, T]` of the system (1.4) with parameters
`α_ε = α`, `β_ε = β`, `γ_ε = γ`, started at `(x, y)`: `W` is an `𝓕`-Brownian motion in
`ℝ^{d1+d2}` and `Z = (X, Y)` solves (1.4) in the Itô sense of `Peng1990.SMP.SolvesSDE`. -/
def IsSolution14 (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (α β γ : ℝ) (T : ℝ≥0) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin (d1 + d2) → ℝ) (Z : ℝ≥0 → Ω → Fin d1 ⊕ Fin d2 → ℝ) : Prop :=
  IsFBrownian 𝓕 P W ∧
  Peng1990.SMP.SolvesSDE 𝓕 P T W (Sum.elim x.ofLp y.ofLp)
    (fun s _ z => drift14 b c F H α β γ s z) (fun j s _ z => diff14 σ G α j s z) Z

/-- `(𝓕, P, W, Ŷ)` is a weak solution on `[0, T]` of the limit equation (2.9),
`dŶ = F̂(t,Ŷ) dt + Ĝ(t,Ŷ) dW²`, `Ŷ_0 = y`, with `W` a `d2`-dimensional `𝓕`-Brownian motion. -/
def IsSolution29 (Fhat : ℝ≥0 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (Ghat : ℝ≥0 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (T : ℝ≥0) (y : FullyCoupledSDE.Poisson.E d2)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W : ℝ≥0 → Ω → Fin d2 → ℝ) (Yh : ℝ≥0 → Ω → Fin d2 → ℝ) : Prop :=
  IsFBrownian 𝓕 P W ∧
  Peng1990.SMP.SolvesSDE 𝓕 P T W y.ofLp
    (fun s _ z => (Fhat s (WithLp.toLp 2 z)).ofLp)
    (fun j s _ z => fun i => Ghat s (WithLp.toLp 2 z) i j) Yh

end SDE

/-! ### The mollifying approximation (4.1), p. 1222 -/

section Mollify

variable {d1 d2 : ℕ}

/-- `ρ^n_1(r) := n² ρ_1(n² r)` (printed `ρ^n_1(y)`, p. 1222). -/
noncomputable def rho1n (ρ1 : ℝ → ℝ) (n : ℕ) (r : ℝ) : ℝ := (n : ℝ) ^ 2 * ρ1 ((n : ℝ) ^ 2 * r)

/-- `ρ^n_2(z) := n^{d2} ρ_2(n z)`. -/
noncomputable def rho2n (ρ2 : FullyCoupledSDE.Poisson.E d2 → ℝ) (n : ℕ) (z : FullyCoupledSDE.Poisson.E d2) : ℝ := (n : ℝ) ^ d2 * ρ2 ((n : ℝ) • z)

/-- (4.1): `f_n(t,x,y) := ∫_{ℝ^{d2+1}} f(t − s, x, y − z) ρ^n_2(z) ρ^n_1(s) dz ds`, the mollification
of `f` in the `t` and `y` variables (as an iterated Lebesgue integral, `s ∈ ℝ`, `z ∈ ℝ^{d2}`). -/
noncomputable def mollify (ρ1 : ℝ → ℝ) (ρ2 : FullyCoupledSDE.Poisson.E d2 → ℝ) (f : ℝ → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ) (n : ℕ)
    (t : ℝ) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2) : ℝ :=
  ∫ s, ∫ z, f (t - s) x (y - z) * rho2n ρ2 n z * rho1n ρ1 n s

end Mollify

/-! ### The parameters -/

/-- The standing assumptions on the small parameters (p. 1206): `α_ε, β_ε, γ_ε > 0` for small
`ε > 0`, `α_ε, β_ε, γ_ε → 0` and `α_ε²/β_ε → 0` as `ε → 0`. -/
def StandingParams (α β γ : ℝ → ℝ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < α ε ∧ 0 < β ε ∧ 0 < γ ε) ∧
  Tendsto α (𝓝[>] 0) (𝓝 0) ∧ Tendsto β (𝓝[>] 0) (𝓝 0) ∧ Tendsto γ (𝓝[>] 0) (𝓝 0) ∧
  Tendsto (fun ε => α ε ^ 2 / β ε) (𝓝[>] 0) (𝓝 0)

/-- Regime 1 of (1.8): `α_ε/γ_ε → 0` and `α_ε²/(β_ε γ_ε) → 0`. -/
def Regime1 (α β γ : ℝ → ℝ) : Prop :=
  Tendsto (fun ε => α ε / γ ε) (𝓝[>] 0) (𝓝 0) ∧
  Tendsto (fun ε => α ε ^ 2 / (β ε * γ ε)) (𝓝[>] 0) (𝓝 0)

end FullyCoupledSDE.DiffApprox


