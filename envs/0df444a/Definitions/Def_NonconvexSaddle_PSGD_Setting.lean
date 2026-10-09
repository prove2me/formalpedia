-- Prove2me | Definitions.Def_NonconvexSaddle_PSGD_Setting
-- name    : NonconvexSaddle_PSGD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:24.527531+00:00
-- url     : https://prove2.me/theorems/b098cf1a-db88-4a58-b2e0-bf2e6b5d8584
-- title:
--   Assumptions A, B, C, $\epsilon$-second-order stationarity, $\mathfrak N$, Algorithm 2 (PSGD), the parameters (8) and the coupling sequences
-- statement:
--   This file fixes every object of the stochastic part of the paper. Throughout, $\mathbb R^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and operators on $\mathbb R^d$ carry the spectral (operator) norm.
--
--   1. **Smoothness (Definitions 1, 2, Assumption A).** A differentiable $f:\mathbb R^d\to\mathbb R$ is $\ell$-gradient Lipschitz if $\|\nabla f(x_1)-\nabla f(x_2)\|\le \ell\|x_1-x_2\|$ for all $x_1,x_2$; a twice-differentiable $f$ is $\rho$-Hessian Lipschitz if $\|\nabla^2 f(x_1)-\nabla^2 f(x_2)\|\le\rho\|x_1-x_2\|$. Assumption A asks for both.
--
--   2. **Minimum eigenvalue and $\epsilon$-second-order stationarity (Definition 9).** For an operator $A$ on $\mathbb R^d$, $\lambda_{\min}(A)=\inf_{\|v\|=1}\langle Av,v\rangle$. A point $x$ is an $\epsilon$-second-order stationary point if
--   $$\|\nabla f(x)\|\le\epsilon\qquad\text{and}\qquad \lambda_{\min}(\nabla^2 f(x))\ge-\sqrt{\rho\epsilon},$$
--   i.e. $\nabla^2 f(x)\succeq-\sqrt{\rho\epsilon}\,I$. The optimal value is $f^\star=\inf_x f(x)$.
--
--   3. **Stochastic gradients (Assumptions B, C).** The oracle returns $g(x;\theta)$ with $\theta\sim\mathcal D$. Assumption B with level $\sigma>0$: for every $x$, $g(x;\cdot)$ is integrable, $\mathbb E\,g(x;\theta)=\nabla f(x)$, and
--   $$\mathbb P\big(\|g(x;\theta)-\nabla f(x)\|\ge t\big)\le 2\exp\!\big(-t^2/(2\sigma^2)\big)\qquad\text{for all } t\ge0.$$
--   Assumption C with constant $\tilde\ell\ge0$: for $\mathcal D$-almost every $\theta$, $\|g(x_1;\theta)-g(x_2;\theta)\|\le\tilde\ell\|x_1-x_2\|$ for all $x_1,x_2$.
--
--   4. **The quantity $\mathfrak N$ (Eq. (4), (8)).**
--   $$\mathfrak N=1+\min\Big\{\frac{\sigma^2}{\epsilon^2}+\frac{\tilde\ell^2}{\ell\sqrt{\rho\epsilon}},\ \frac{\sigma^2 d}{\epsilon^2}\Big\},$$
--   where $\tilde\ell=+\infty$ encodes that Assumption C fails. A number $N$ is a value of $\mathfrak N$ if $N=1+\sigma^2d/\epsilon^2$ (the case $\tilde\ell=+\infty$), or if $N$ is given by the formula for some $\tilde\ell$ for which Assumption C holds.
--
--   5. **PSGD (Algorithm 2).** The randomness is a sequence $\omega=((\theta_t,\xi_t))_{t\ge0}$ of independent pairs, $\theta_t\sim\mathcal D$ and $\xi_t\sim\mathcal N(0,(r^2/d)I)$ independent, i.i.d. in $t$. From $x_0$, PSGD with step size $\eta$ and perturbation radius $r$ runs
--   $$x_{t+1}=x_t-\eta\big(g(x_t;\theta_t)+\xi_t\big).$$
--
--   6. **Parameters (Eq. (8)).** For a log factor $\iota>0$:
--   $$\eta=\frac{1}{\iota^9\,\ell\mathfrak N},\quad r=\iota\,\epsilon\sqrt{\mathfrak N},\quad \mathscr T=\Big\lceil\frac{\iota}{\eta\sqrt{\rho\epsilon}}\Big\rceil,\quad \mathscr F=\frac{1}{\iota^5}\sqrt{\frac{\epsilon^3}{\rho}},\quad \mathscr S=\frac{2}{\iota^2}\sqrt{\frac{\epsilon}{\rho}},$$
--   and the iteration count of the proof of Theorem 16, $T=\lceil 100\max\{\Delta_f\mathscr T/\mathscr F,\ \Delta_f/(\eta\epsilon^2)\}\rceil$ with $\Delta_f=f(x_0)-f^\star$. The number $Q=d\,\mathfrak N\max\{1,\ell\Delta_f/\epsilon^2\}\,(\ell/\sqrt{\rho\epsilon})/\delta$ is the argument of the logarithm that calibrates $\iota$ in Theorem 16.
--
--   7. **Coupling sequences (Definition 26) and Lemma 28's terms.** For a unit vector $e_1$, the coupled randomness keeps $\theta_\tau$ and the component of $\xi_\tau$ orthogonal to $e_1$ and flips $e_1^\top\xi_\tau$: $\xi'_\tau=\xi_\tau-2\langle e_1,\xi_\tau\rangle e_1$. With $\mathcal H=\nabla^2 f(x_0)$, two runs $x,x'$ and $\hat x_t=x_t-x'_t$,
--   $$\Delta_t=\int_0^1\nabla^2 f(\psi x_t+(1-\psi)x'_t)\,d\psi-\mathcal H,\qquad q(t)=\eta\sum_{\tau=0}^{t-1}(I-\eta\mathcal H)^{t-1-\tau}v_\tau,$$
--   with $v_\tau=\Delta_\tau\hat x_\tau$ for $q_h$, $v_\tau=\hat\zeta_\tau=\zeta_\tau-\zeta'_\tau$ for $q_{sg}$ (where $\zeta_\tau=g(x_\tau;\theta_\tau)-\nabla f(x_\tau)$, $\zeta'_\tau=g(x'_\tau;\theta_\tau)-\nabla f(x'_\tau)$), and $v_\tau=\hat\xi_\tau=\xi_\tau-\xi'_\tau$ for $q_p$.
--
--   8. **Lemma 29's functions.** With $a=\eta\gamma$: $\alpha(t)=\big[\sum_{\tau=0}^{t-1}(1+a)^{2(t-1-\tau)}\big]^{1/2}$ and $\beta(t)=(1+a)^t/\sqrt{2a}$.
--
--   These are the objects in which Theorem 16 and all the lemmas of Appendix B are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; the Hessian is the derivative of the gradient map, and $\lambda_{\min}$ is the Rayleigh-quotient infimum over the unit sphere (Lean returns $0$ for $d=0$, so every statement assumes $d\ge1$). Assumption B is required for $t\ge0$ because the printed "$\forall t\in\mathbb R$" is unsatisfiable for negative $t$, and $\sigma>0$ is part of it because at $\sigma=0$ Lean's division by zero would make the tail bound vacuous; integrability is stated explicitly because Lean's integral of a non-integrable function is $0$. Assumption C is required almost surely instead of on $\operatorname{supp}\mathcal D$, which is no stronger. The paper's $\mathscr T=\iota/(\eta\sqrt{\rho\epsilon})$ and $T$ are rounded up to integers. The randomness is the infinite product measure `Measure.infinitePi`, and $\mathcal N(0,(r^2/d)I)$ is the standard Gaussian of `EuclideanSpace` scaled by $r/\sqrt d$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, pp. 5–8, 10–11, 23, 25–26, 28: Definitions 1, 2, 9, Assumptions A, B, C, Eq. (4), Algorithm 2, Eq. (8), Definition 26, Lemmas 28–29, proof of Theorem 16

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

/-- The Euclidean space `ℝ^d` with the `ℓ₂` norm (Jin–Netrapalli–Ge–Kakade–Jordan,
arXiv:1902.04811v2, §2.1, p. 5). -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The Hessian `∇²f(x)` of `f : ℝ^d → ℝ`, as the derivative of the gradient map: a linear operator
`ℝ^d → ℝ^d`, whose operator norm is the spectral norm of §2.1 (p. 5). -/
noncomputable def hess {d : ℕ} (f : E d → ℝ) (x : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (gradient f) x

/-- The smallest eigenvalue `λ_min(A)` of an operator on `ℝ^d` (§2.1, p. 5), written as the
Rayleigh-quotient infimum `inf_{‖v‖ = 1} ⟪A v, v⟫`. For self-adjoint `A` and `d ≥ 1` this is the
smallest eigenvalue; the quadratic form is bounded below by `−‖A‖` on the nonempty unit sphere, so
the infimum is a genuine (attained) minimum. For `d = 0` Lean's empty infimum is `0`; every
statement using it assumes `1 ≤ d`. (Same body as the published `CubicNewton.Shared.lamMin`.) -/
noncomputable def lamMin {d : ℕ} (A : E d →L[ℝ] E d) : ℝ :=
  ⨅ v : Metric.sphere (0 : E d) 1, ⟪A v, v⟫

/-- Definition 1 (p. 6): a differentiable `f` is `ℓ`-gradient Lipschitz if
`‖∇f(x₁) − ∇f(x₂)‖ ≤ ℓ‖x₁ − x₂‖` for all `x₁, x₂`. -/
def IsGradLipschitz {d : ℕ} (f : E d → ℝ) (ℓ : ℝ) : Prop :=
  Differentiable ℝ f ∧ ∀ x₁ x₂ : E d, ‖gradient f x₁ - gradient f x₂‖ ≤ ℓ * ‖x₁ - x₂‖

/-- Definition 2 (p. 6): a twice-differentiable `f` (here: `f` and its gradient map are
differentiable) is `ρ`-Hessian Lipschitz if `‖∇²f(x₁) − ∇²f(x₂)‖ ≤ ρ‖x₁ − x₂‖` for all `x₁, x₂`, in
operator norm. -/
def IsHessLipschitz {d : ℕ} (f : E d → ℝ) (ρ : ℝ) : Prop :=
  Differentiable ℝ f ∧ Differentiable ℝ (gradient f) ∧
    ∀ x₁ x₂ : E d, ‖hess f x₁ - hess f x₂‖ ≤ ρ * ‖x₁ - x₂‖

/-- Assumption A (p. 6): `f` is `ℓ`-gradient Lipschitz and `ρ`-Hessian Lipschitz. -/
def AssumptionA {d : ℕ} (f : E d → ℝ) (ℓ ρ : ℝ) : Prop :=
  IsGradLipschitz f ℓ ∧ IsHessLipschitz f ρ

/-- Definition 9 (p. 7): `x` is an `ε`-second-order stationary point if `‖∇f(x)‖ ≤ ε` and
`∇²f(x) ⪰ −√(ρε)·I`, i.e. `λ_min(∇²f(x)) ≥ −√(ρε)`. -/
def IsEpsSOSP {d : ℕ} (f : E d → ℝ) (ρ ε : ℝ) (x : E d) : Prop :=
  ‖gradient f x‖ ≤ ε ∧ -Real.sqrt (ρ * ε) ≤ lamMin (hess f x)

/-- The global minimum value `f⋆ = inf_x f(x)` (§2.1, p. 6); it is the infimum of `f` only when `f`
is bounded below, which every statement using it assumes. -/
noncomputable def fstar {d : ℕ} (f : E d → ℝ) : ℝ :=
  ⨅ x : E d, f x

/-- Assumption B (p. 8) for the stochastic gradient oracle `g(x; θ)`, `θ ∼ 𝒟`, with noise level `σ`:
for every `x`, `g(x; ·)` is `𝒟`-integrable with mean `∇f(x)`, and
`P(‖g(x; θ) − ∇f(x)‖ ≥ t) ≤ 2 exp(−t²/(2σ²))` for every `t ≥ 0`.

The page writes "`∀ t ∈ ℝ`", which no oracle satisfies (for `t < 0` the left side is `1` while the
right side is `< 1` once `|t| > σ√(2 ln 2)`); the bound is required for `t ≥ 0`. `σ > 0` is part of
the assumption: at `σ = 0` Lean's `t²/(2·0²) = 0` would turn the tail bound into the vacuous `≤ 2`. -/
structure AssumptionB {d : ℕ} {Θ : Type} [MeasurableSpace Θ] (f : E d → ℝ) (g : E d → Θ → E d)
    (𝒟 : Measure Θ) (σ : ℝ) : Prop where
  sigma_pos : 0 < σ
  integrable : ∀ x : E d, Integrable (g x) 𝒟
  unbiased : ∀ x : E d, ∫ θ, g x θ ∂𝒟 = gradient f x
  tail : ∀ x : E d, ∀ t : ℝ, 0 ≤ t →
    𝒟 {θ | t ≤ ‖g x θ - gradient f x‖} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2)))

/-- Assumption C (p. 10): for (almost) every `θ` in the support of `𝒟`, `g(·; θ)` is `ℓ̃`-Lipschitz,
`‖g(x₁; θ) − g(x₂; θ)‖ ≤ ℓ̃‖x₁ − x₂‖`, with `ℓ̃ ≥ 0`. -/
def AssumptionC {d : ℕ} {Θ : Type} [MeasurableSpace Θ] (g : E d → Θ → E d) (𝒟 : Measure Θ)
    (ℓt : ℝ) : Prop :=
  0 ≤ ℓt ∧ ∀ᵐ θ ∂𝒟, ∀ x₁ x₂ : E d, ‖g x₁ θ - g x₂ θ‖ ≤ ℓt * ‖x₁ - x₂‖

/-- The quantity `𝔑` of Eq. (4) (p. 11) and Eq. (8) (p. 23):
`𝔑 = 1 + min{σ²/ε² + ℓ̃²/(ℓ√(ρε)), σ²d/ε²}`, where `ℓ̃ = +∞` encodes that Assumption C fails
(p. 11). `IsFrakN … N` says `N` is a value of `𝔑`: either the `ℓ̃ = +∞` value
`1 + σ²d/ε²`, or the value for some `ℓ̃` for which Assumption C holds. -/
def IsFrakN {d : ℕ} {Θ : Type} [MeasurableSpace Θ] (g : E d → Θ → E d) (𝒟 : Measure Θ)
    (ℓ ρ σ ε N : ℝ) : Prop :=
  N = 1 + σ ^ 2 * d / ε ^ 2 ∨
    ∃ ℓt : ℝ, AssumptionC g 𝒟 ℓt ∧
      N = 1 + min (σ ^ 2 / ε ^ 2 + ℓt ^ 2 / (ℓ * Real.sqrt (ρ * ε))) (σ ^ 2 * d / ε ^ 2)

/-- The perturbation law `𝒩(0, (r²/d) I)` of Algorithm 2 (p. 11): the image of the standard Gaussian
on `ℝ^d` under `z ↦ (r/√d) z`. -/
noncomputable def gaussPert (d : ℕ) (r : ℝ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun z => (r / Real.sqrt d) • z)

/-- The law of the randomness of Algorithm 2 (p. 11): a sequence `ω = ((θ_t, ξ_t))_{t ∈ ℕ}` of
independent pairs, with `θ_t ∼ 𝒟` and `ξ_t ∼ 𝒩(0, (r²/d) I)` independent of each other and i.i.d.
across `t`. -/
noncomputable def noiseLaw {d : ℕ} {Θ : Type} [MeasurableSpace Θ] (𝒟 : Measure Θ) (r : ℝ) :
    Measure (ℕ → Θ × E d) :=
  Measure.infinitePi (fun _ : ℕ => 𝒟.prod (gaussPert d r))

/-- The run of PSGD, Algorithm 2 (p. 11), on the randomness `ω`: `x₀` given and
`x_{t+1} = x_t − η (g(x_t; θ_t) + ξ_t)` with `(θ_t, ξ_t) = ω t`. -/
noncomputable def psgd {d : ℕ} {Θ : Type} (g : E d → Θ → E d) (η : ℝ) (x₀ : E d)
    (ω : ℕ → Θ × E d) : ℕ → E d
  | 0 => x₀
  | t + 1 => psgd g η x₀ ω t - η • (g (psgd g η x₀ ω t) (ω t).1 + (ω t).2)

/-- Step size of Eq. (8) (p. 23): `η = 1/(ι⁹ · ℓ𝔑)`. -/
noncomputable def etaP (ι ℓ N : ℝ) : ℝ := 1 / (ι ^ 9 * (ℓ * N))

/-- Perturbation radius of Eq. (8) (p. 23): `r = ι · ε√𝔑`. -/
noncomputable def rP (ι ε N : ℝ) : ℝ := ι * (ε * Real.sqrt N)

/-- Escape time of Eq. (8) (p. 23), `𝒯 := ι/(η√(ρε))`, rounded up to a natural number. -/
noncomputable def TcalP (ι η ρ ε : ℝ) : ℕ := ⌈ι / (η * Real.sqrt (ρ * ε))⌉₊

/-- Function decrease of Eq. (8) (p. 23): `ℱ := (1/ι⁵)√(ε³/ρ)`. -/
noncomputable def FcalP (ι ρ ε : ℝ) : ℝ := 1 / ι ^ 5 * Real.sqrt (ε ^ 3 / ρ)

/-- Localization radius of Eq. (8) (p. 23): `𝒮 := (2/ι²)√(ε/ρ)`. -/
noncomputable def ScalP (ι ρ ε : ℝ) : ℝ := 2 / ι ^ 2 * Real.sqrt (ε / ρ)

/-- The iteration count of the proof of Theorem 16 (p. 28),
`T = 100 max{(f(x₀) − f⋆)𝒯/ℱ, (f(x₀) − f⋆)/(ηε²)}`, rounded up to a natural number. -/
noncomputable def iterT (Δf Tcal Fcal η ε : ℝ) : ℕ :=
  ⌈100 * max (Δf * Tcal / Fcal) (Δf / (η * ε ^ 2))⌉₊

/-- The scale-invariant argument of the logarithm that pins `ι` in the statement of Theorem 16:
`Q = d · 𝔑 · max{1, ℓΔ_f/ε²} · (ℓ/√(ρε)) / δ` (replacing the paper's `dℓΔ_f𝔑/(ρεδ)`, see the
Formalization Note of Theorem 16). -/
noncomputable def logArgQ (d : ℕ) (ℓ ρ ε δ N Δf : ℝ) : ℝ :=
  d * N * max 1 (ℓ * Δf / ε ^ 2) * (ℓ / Real.sqrt (ρ * ε)) / δ

/-- Reflection of a perturbation in the direction `e₁`: `ξ ↦ ξ − 2⟪e₁, ξ⟫e₁`. For a unit `e₁` it keeps
the component `𝒫₋₁ξ` orthogonal to `e₁` and flips `e₁ᵀξ`. -/
noncomputable def reflect {d : ℕ} (e₁ ξ : E d) : E d :=
  ξ - (2 * ⟪e₁, ξ⟫) • e₁

/-- The randomness of the coupled run of Definition 26 (p. 25): the same `θ_τ`, and the perturbation
`ξ'_τ` with the same component orthogonal to `e₁` and `e₁ᵀξ'_τ = −e₁ᵀξ_τ`. -/
noncomputable def couple {d : ℕ} {Θ : Type} (e₁ : E d) (ω : ℕ → Θ × E d) : ℕ → Θ × E d :=
  fun τ => ((ω τ).1, reflect e₁ (ω τ).2)

/-- The propagated sum `η Σ_{τ=0}^{t−1} (I − ηℋ)^{t−1−τ} v_τ` of Lemma 28 (p. 26). -/
noncomputable def propSum {d : ℕ} (ℋ : E d →L[ℝ] E d) (η : ℝ) (v : ℕ → E d) (t : ℕ) : E d :=
  η • ∑ τ ∈ Finset.range t, ((ContinuousLinearMap.id ℝ (E d) - η • ℋ) ^ (t - 1 - τ)) (v τ)

/-- `Δ_t := ∫₀¹ ∇²f(ψx_t + (1 − ψ)x'_t) dψ − ℋ` of Lemma 28 (p. 26), for two points `x, x'`. -/
noncomputable def hessDelta {d : ℕ} (f : E d → ℝ) (ℋ : E d →L[ℝ] E d) (x x' : E d) :
    E d →L[ℝ] E d :=
  (∫ ψ in (0 : ℝ)..1, hess f (ψ • x + (1 - ψ) • x')) - ℋ

/-- `q_h(t) = η Σ_{τ<t} (I − ηℋ)^{t−1−τ} Δ_τ x̂_τ` of Lemma 28 (p. 26), for runs `x`, `x'`. -/
noncomputable def qh {d : ℕ} (f : E d → ℝ) (ℋ : E d →L[ℝ] E d) (η : ℝ) (x x' : ℕ → E d)
    (t : ℕ) : E d :=
  propSum ℋ η (fun τ => hessDelta f ℋ (x τ) (x' τ) (x τ - x' τ)) t

/-- `q_sg(t) = η Σ_{τ<t} (I − ηℋ)^{t−1−τ} ζ̂_τ` of Lemma 28 (p. 26), where
`ζ̂_τ = ζ_τ − ζ'_τ`, `ζ_τ = g(x_τ; θ_τ) − ∇f(x_τ)` and `ζ'_τ = g(x'_τ; θ_τ) − ∇f(x'_τ)` (the coupled
runs share `θ_τ`). -/
noncomputable def qsg {d : ℕ} {Θ : Type} (f : E d → ℝ) (g : E d → Θ → E d) (ℋ : E d →L[ℝ] E d)
    (η : ℝ) (ω : ℕ → Θ × E d) (x x' : ℕ → E d) (t : ℕ) : E d :=
  propSum ℋ η (fun τ => (g (x τ) (ω τ).1 - gradient f (x τ)) -
    (g (x' τ) (ω τ).1 - gradient f (x' τ))) t

/-- `q_p(t) = η Σ_{τ<t} (I − ηℋ)^{t−1−τ} ξ̂_τ` of Lemma 28 (p. 26), where `ξ̂_τ = ξ_τ − ξ'_τ` for the
perturbations `ξ_τ = (ω τ).2` and `ξ'_τ = (ω' τ).2`. -/
noncomputable def qp {d : ℕ} {Θ : Type} (ℋ : E d →L[ℝ] E d) (η : ℝ) (ω ω' : ℕ → Θ × E d)
    (t : ℕ) : E d :=
  propSum ℋ η (fun τ => (ω τ).2 - (ω' τ).2) t

/-- `α(t) := [Σ_{τ=0}^{t−1} (1 + ηγ)^{2(t−1−τ)}]^{1/2}` of Lemma 29 (p. 26), with `a = ηγ`. -/
noncomputable def alphaL (a : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (∑ τ ∈ Finset.range t, (1 + a) ^ (2 * (t - 1 - τ)))

/-- `β(t) := (1 + ηγ)^t/√(2ηγ)` of Lemma 29 (p. 26), with `a = ηγ`. -/
noncomputable def betaL (a : ℝ) (t : ℕ) : ℝ :=
  (1 + a) ^ t / Real.sqrt (2 * a)

end NonconvexSaddle.PSGD


