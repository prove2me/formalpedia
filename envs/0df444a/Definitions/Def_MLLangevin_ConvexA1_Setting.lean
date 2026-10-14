-- Prove2me | Definitions.Def_MLLangevin_ConvexA1_Setting
-- name    : MLLangevin_ConvexA1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:27.6521+00:00
-- url     : https://prove2.me/theorems/bb2d4d7f-d75d-4bec-8fd4-3ea6ce298067
-- title:
--   §2.2–§2.4, (2), (7), (12), (55), (H₁)–(H₄), pp. 1–9, 28–33 — additive Euler scheme, diffusion, invariant laws, multilevel estimator 𝒴, cost, Υ₁, β₁, c₁
-- statement:
--   This file fixes the objects of the strongly contractive additive setting of Egéa and Panloup.
--
--   Throughout, $\mathbb R^d$ carries the Euclidean norm $|\cdot|$ and inner product $\langle\cdot,\cdot\rangle$, $b:\mathbb R^d\to\mathbb R^d$ is the drift, $\sigma>0$ is a scalar noise level and $W=(W_t)_{t\ge0}$ is a standard $d$-dimensional Brownian motion on a probability space $(\Omega,\mathcal F,\mathbb P)$.
--
--   1. **Assumption $(\mathbf C_\alpha)$.** For all $x,y\in\mathbb R^d$, $\langle b(y)-b(x),y-x\rangle\le-\alpha|x-y|^2$.
--   2. **Euler scheme.** For a step $\gamma>0$ and a start $x$, $\bar X^{\gamma,x}_0=x$ and
--   $$\bar X^{\gamma,x}_{(n+1)\gamma}=\bar X^{\gamma,x}_{n\gamma}+\gamma\, b(\bar X^{\gamma,x}_{n\gamma})+\sigma\,(W_{(n+1)\gamma}-W_{n\gamma}).$$
--   Its continuous-time interpolation is $\bar X^{\gamma,x}_t=\bar X^{\gamma,x}_{\underline t}+(t-\underline t)\,b(\bar X^{\gamma,x}_{\underline t})+\sigma(W_t-W_{\underline t})$ with $\underline t=\gamma\lfloor t/\gamma\rfloor$, i.e. the solution of $\bar X_t=x+\int_0^t b(\bar X_{\underline s})\,ds+\sigma W_t$.
--   3. **Diffusion.** $X^x$ is a pathwise solution of $X^x_t=x+\int_0^t b(X^x_s)\,ds+\sigma W_t$ with continuous paths. A probability $\pi$ is *invariant for the diffusion* if $\int\mathbb P(X^x_t\in A)\,\pi(dx)=\pi(A)$ for all $t\ge0$ and Borel $A$; a probability $\pi^\gamma$ is *invariant for the scheme* if $\int\mathbb P(\bar X^{\gamma,x}_\gamma\in A)\,\pi^\gamma(dx)=\pi^\gamma(A)$.
--   4. **Lipschitz constant.** $[f]_1=\inf\{K\ge0:|f(x)-f(y)|\le K|x-y|\ \forall x,y\}$.
--   5. **Multilevel occupation measure (7).** Given $x_0$, $\gamma_0$, $R$, $\tau$, horizons $(T_r)_{0\le r\le R}$, steps $\gamma_r=\gamma_0 2^{-r}$ and Brownian motions $B^{(0)},B^{(1)},\dots$,
--   $$\mathcal Y(f)=\frac1{T_0-\tau}\int_\tau^{T_0}f\big(\bar X^{\gamma_0,x_0,B^{(0)}}_{\underline s_{\gamma_0}}\big)ds+\sum_{r=1}^R\frac1{T_r-\tau}\int_\tau^{T_r}\Big(f\big(\bar X^{\gamma_r,x_0,B^{(r)}}_{\underline s_{\gamma_{r-1}}}\big)-f\big(\bar X^{\gamma_{r-1},x_0,B^{(r)}}_{\underline s_{\gamma_{r-1}}}\big)\Big)ds,$$
--   with cost $\mathcal C(\mathcal Y)=T_0/\gamma_0+\sum_{r=1}^R(T_r/\gamma_r+T_r/\gamma_{r-1})$.
--   6. **Assumptions $(\mathbf H_1)$–$(\mathbf H_4)$** for the scheme driven by $W$, with $\eta_0>0$: $(\mathbf H_1)$ $|\mathbb E f(\bar X^{\gamma,x}_{n\gamma})-\pi^\gamma(f)|\le c_1(x)[f]_1e^{-\alpha n\gamma}$; $(\mathbf H_2)$ $c_2>0$ and $\|\bar X^{\gamma,x_0}_{n\gamma}-\bar X^{\gamma/2,x_0}_{n\gamma}\|_2\le c_2\gamma^{\mathfrak a/2}$; $(\mathbf H_3)$ $c_3>0$ and $|\pi(f)-\pi^\gamma(f)|\le c_3[f]_1\gamma^\delta$; $(\mathbf H_4)$ $c_4\ge0$ and $\sup_{t\ge0}(\|\bar X^{\gamma,x_0}_t-x_0\|_2+\|c_1(\bar X^{\gamma,x_0}_t)\|_2)\le c_4$; each for every $\gamma\in(0,\eta_0]$, every $n\ge0$ and every scheme-invariant probability $\pi^\gamma$; $(\mathbf H_1)$ and $(\mathbf H_3)$ also require that a scheme-invariant probability $\pi^\gamma$ exists for every $\gamma\in(0,\eta_0]$.
--   7. **Parameters.** $R_\varepsilon=\lceil\delta^{-1}\log_2(r_0\varepsilon^{-1})\rceil$; $T_r=\mathfrak t\varepsilon^{-2}2^{-\frac{1+\mathfrak a}2r}$ if $\mathfrak a>1$ and $\mathfrak t\varepsilon^{-2}R^22^{-r}$ if $\mathfrak a=1$; $\mathfrak c_{\mathfrak a}=1+\frac32(2^{(\mathfrak a-1)/2}-1)^{-1}$ ($\mathfrak a>1$), $\frac52$ ($\mathfrak a=1$); $\mathfrak d_{\mathfrak a}=(\mathfrak a-1)^{-2}$ ($\mathfrak a>1$), $1$ ($\mathfrak a=1$); $\tau_1=\frac{1+\mathfrak a-2\delta}{\alpha\delta}$, $\tau_2=0\vee\alpha^{-1}\log(r_0^{(1+\mathfrak a)/(2\delta)}(\mathfrak d_{\mathfrak a}c_4)^{-1})$.
--   8. **Constants.** $\Upsilon_1^2=1\vee(\alpha^{-2}|b(x_0)|^2+\alpha^{-1}\sigma^2d)$; $\beta_1(x)=\frac{L^2}\alpha|x-x^\star|^2+2|b(x^\star)|^2(\frac1\alpha+\frac{L^2}{\alpha^3})+\frac{3L^2\sigma^2d}{\alpha^2}$; $c_1(x)=|x-x^\star|+\sqrt{|b(x^\star)|^2(\frac1{L^2}+\frac2{\alpha^2})+\frac{2\sigma^2d}\alpha}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The Brownian motion is the published `EthierKurtz.IsStandardBrownian`. $(\mathbf H_1)$–$(\mathbf H_3)$ are stated at grid times $n\gamma$ (as on the page, where $\underline t_\gamma$ ranges over the grid); $(\mathbf H_4)$ is stated for all $t\ge0$ of the continuous-time scheme, as on the page. In $(\mathbf H_1)$ and $(\mathbf H_3)$, $\pi^\gamma$ ranges over every scheme-invariant probability (Lemma 5.1 (i) shows there is exactly one), and both predicates include the existence of one for every $\gamma\in(0,\eta_0]$, which the paper assumes implicitly (p. 7); without it a statement concluding $(\mathbf H_1)$ would hold vacuously when no $\pi^\gamma$ exists. The cost formula of p. 6 is used for all horizons, not only multiples of the steps. $\mathfrak c_{\mathfrak a}$, $\mathfrak d_{\mathfrak a}$ are explicit case splits, so no division by zero occurs at $\mathfrak a=1$.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, (2), (4), (7) and cost §2.2, pp. 1–2, 6; (H₁)–(H₄), pp. 6–7; (8), p. 7; (C_α) and (12), p. 9; (39)–(40), p. 26; Lemma 5.1 (ii) c₁, p. 29; (55), p. 32; Proposition 5.1 (i) β₁, p. 33

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Assumption (C_α), p. 9: `⟨b(y) − b(x), y − x⟩ ≤ −α|x − y|²` for all `x, y`. -/
def CondC (b : SDEState d → SDEState d) (α : ℝ) : Prop :=
  ∀ x y : SDEState d, inner ℝ (b y - b x) (y - x) ≤ -α * ‖x - y‖ ^ 2

/-- The grid time `nγ` as a nonnegative real. -/
noncomputable def gridTime (n : ℕ) (γ : ℝ) : ℝ≥0 := Real.toNNReal ((n : ℝ) * γ)

/-- The additive Euler scheme (2) at its grid points `nγ`, started at `x` and driven by `W`:
`X̄₀ = x`, `X̄_{(n+1)γ} = X̄_{nγ} + γ b(X̄_{nγ}) + σ (W_{(n+1)γ} − W_{nγ})`. -/
noncomputable def eulerChain (b : SDEState d → SDEState d) (σ γ : ℝ) (x : SDEState d)
    (W : ℝ≥0 → Ω → SDEState d) : ℕ → Ω → SDEState d
  | 0 => fun _ => x
  | n + 1 => fun ω =>
      eulerChain b σ γ x W n ω + γ • b (eulerChain b σ γ x W n ω) +
        σ • (W (gridTime (n + 1) γ) ω - W (gridTime n γ) ω)

/-- The genuine continuous-time additive Euler scheme (55): for `t ∈ [nγ, (n+1)γ)`,
`X̄_t = X̄_{nγ} + (t − nγ) b(X̄_{nγ}) + σ (W_t − W_{nγ})`, with `n = ⌊t/γ⌋`. -/
noncomputable def eulerCont (b : SDEState d → SDEState d) (σ γ : ℝ) (x : SDEState d)
    (W : ℝ≥0 → Ω → SDEState d) (t : ℝ≥0) (ω : Ω) : SDEState d :=
  eulerChain b σ γ x W ⌊(t : ℝ) / γ⌋₊ ω +
    ((t : ℝ) - (⌊(t : ℝ) / γ⌋₊ : ℝ) * γ) • b (eulerChain b σ γ x W ⌊(t : ℝ) / γ⌋₊ ω) +
    σ • (W t ω - W (gridTime ⌊(t : ℝ) / γ⌋₊ γ) ω)

/-- `X` is a pathwise solution of the additive SDE `X_t = x + ∫₀ᵗ b(X_s) ds + σ W_t`
(pp. 30, 32): continuous paths and the integral equation for every `ω` and `t`. -/
def IsAddSolution (b : SDEState d → SDEState d) (σ : ℝ) (W : ℝ≥0 → Ω → SDEState d)
    (x : SDEState d) (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  (∀ ω, Continuous fun t => X t ω) ∧
  ∀ ω (t : ℝ≥0), X t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), b (X s.toNNReal ω)) + σ • W t ω

/-- `π` is invariant for the transition semigroup of the diffusion whose solution started at
`x` is `Xsol x`: `∫ P(X^x_t ∈ A) π(dx) = π(A)` for every `t ≥ 0` and Borel `A`. -/
def IsInvDiffusion (P : Measure Ω) (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d)
    (π : Measure (SDEState d)) : Prop :=
  ∀ (t : ℝ≥0) (A : Set (SDEState d)), MeasurableSet A →
    ∫⁻ x, P {ω | Xsol x t ω ∈ A} ∂π = π A

/-- `πγ` is invariant for one step of the Euler scheme with step `γ`:
`∫ P(X̄^{γ,x}_γ ∈ A) πγ(dx) = πγ(A)` for every Borel `A`. -/
def IsInvChain (P : Measure Ω) (b : SDEState d → SDEState d) (σ γ : ℝ)
    (W : ℝ≥0 → Ω → SDEState d) (πγ : Measure (SDEState d)) : Prop :=
  ∀ A : Set (SDEState d), MeasurableSet A →
    ∫⁻ x, P {ω | eulerChain b σ γ x W 1 ω ∈ A} ∂πγ = πγ A

/-- `[f]₁`, the least Lipschitz constant of `f` (p. 5). -/
noncomputable def lipConst (f : SDEState d → ℝ) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ ∀ x y, |f x - f y| ≤ K * ‖x - y‖}

/-- The multilevel occupation measure (7) applied to `f`: level `0` runs the scheme with step
`γ₀` on `B 0`; level `r ≥ 1` runs the schemes with steps `γ₀2^{-r}` and `γ₀2^{-(r-1)}` on the
same motion `B r`, both read at the coarse grid times `s̲_{γ_{r-1}}`. -/
noncomputable def estimator (b : SDEState d → SDEState d) (σ : ℝ) (x₀ : SDEState d) (γ₀ : ℝ)
    (R : ℕ) (τ : ℝ) (T : ℕ → ℝ) (B : ℕ → ℝ≥0 → Ω → SDEState d) (f : SDEState d → ℝ)
    (ω : Ω) : ℝ :=
  (T 0 - τ)⁻¹ * (∫ s in τ..T 0, f (eulerChain b σ γ₀ x₀ (B 0) ⌊s / γ₀⌋₊ ω)) +
  ∑ r ∈ Finset.Icc 1 R, (T r - τ)⁻¹ *
    ∫ s in τ..T r,
      (f (eulerChain b σ (γ₀ / 2 ^ r) x₀ (B r) (2 * ⌊s / (γ₀ / 2 ^ (r - 1))⌋₊) ω) -
        f (eulerChain b σ (γ₀ / 2 ^ (r - 1)) x₀ (B r) ⌊s / (γ₀ / 2 ^ (r - 1))⌋₊ ω))

/-- The complexity `𝒞(𝒴) = T₀/γ₀ + Σ_{r=1}^R (T_r/γ_r + T_r/γ_{r-1})` (p. 6). -/
noncomputable def cost (R : ℕ) (γ₀ : ℝ) (T : ℕ → ℝ) : ℝ :=
  T 0 / γ₀ + ∑ r ∈ Finset.Icc 1 R, (T r / (γ₀ / 2 ^ r) + T r / (γ₀ / 2 ^ (r - 1)))

/-- (H₁), grid times, for the scheme driven by `W`: for every `γ ∈ (0, η₀]` the step-`γ` scheme
has an invariant probability (p. 7: "we implicitly assume that `π^γ` exists"), and for every
invariant probability `πγ` of it, every `x` and `n`,
`|𝔼 f(X̄^{γ,x}_{nγ}) − πγ(f)| ≤ c₁(x) [f]₁ e^{−α nγ}`. -/
def H1 (P : Measure Ω) (b : SDEState d → SDEState d) (σ : ℝ) (W : ℝ≥0 → Ω → SDEState d)
    (f : SDEState d → ℝ) (α η₀ : ℝ) (c₁ : SDEState d → ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ ≤ η₀ →
    (∃ πγ : Measure (SDEState d), IsProbabilityMeasure πγ ∧ IsInvChain P b σ γ W πγ) ∧
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ →
    IsInvChain P b σ γ W πγ → ∀ (x : SDEState d) (n : ℕ),
      |(∫ ω, f (eulerChain b σ γ x W n ω) ∂P) - ∫ y, f y ∂πγ| ≤
        c₁ x * lipConst f * Real.exp (-α * ((n : ℝ) * γ))

/-- (H₂): `c₂ > 0` and for every `γ ∈ (0, η₀]` and `n`,
`‖X̄^{γ,x₀}_{nγ} − X̄^{γ/2,x₀}_{nγ}‖₂ ≤ c₂ γ^{𝔞/2}` (both schemes on `W`). -/
def H2 (P : Measure Ω) (b : SDEState d → SDEState d) (σ : ℝ) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (η₀ 𝔞 c₂ : ℝ) : Prop :=
  0 < c₂ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ η₀ → ∀ n : ℕ,
    eLpNorm (fun ω => eulerChain b σ γ x₀ W n ω - eulerChain b σ (γ / 2) x₀ W (2 * n) ω) 2 P ≤
      ENNReal.ofReal (c₂ * γ ^ (𝔞 / 2))

/-- (H₃): `c₃ > 0` and for every `γ ∈ (0, η₀]` the step-`γ` scheme has an invariant
probability, and for every invariant probability `πγ` of it, `|π(f) − πγ(f)| ≤ c₃ [f]₁ γ^δ`. -/
def H3 (P : Measure Ω) (b : SDEState d → SDEState d) (σ : ℝ) (W : ℝ≥0 → Ω → SDEState d)
    (f : SDEState d → ℝ) (π : Measure (SDEState d)) (η₀ δ c₃ : ℝ) : Prop :=
  0 < c₃ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ η₀ →
    (∃ πγ : Measure (SDEState d), IsProbabilityMeasure πγ ∧ IsInvChain P b σ γ W πγ) ∧
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ →
    IsInvChain P b σ γ W πγ → |(∫ y, f y ∂π) - ∫ y, f y ∂πγ| ≤ c₃ * lipConst f * γ ^ δ

/-- (H₄), over all `t ≥ 0` of the continuous-time scheme: `c₄ ≥ 0` and for every
`γ ∈ (0, η₀]`, `‖X̄^{γ,x₀}_t − x₀‖₂ + ‖c₁(X̄^{γ,x₀}_t)‖₂ ≤ c₄`. -/
def H4 (P : Measure Ω) (b : SDEState d → SDEState d) (σ : ℝ) (W : ℝ≥0 → Ω → SDEState d)
    (x₀ : SDEState d) (η₀ : ℝ) (c₁ : SDEState d → ℝ) (c₄ : ℝ) : Prop :=
  0 ≤ c₄ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ η₀ → ∀ t : ℝ≥0,
    eLpNorm (fun ω => eulerCont b σ γ x₀ W t ω - x₀) 2 P +
      eLpNorm (fun ω => c₁ (eulerCont b σ γ x₀ W t ω)) 2 P ≤ ENNReal.ofReal c₄

/-- `𝔠_𝔞 = 1 + (3/2)(2^{(𝔞−1)/2} − 1)⁻¹` if `𝔞 > 1`, `5/2` if `𝔞 = 1` (Theorem 2.1, p. 8). -/
noncomputable def ca (𝔞 : ℝ) : ℝ :=
  if 1 < 𝔞 then 1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹ else 5 / 2

/-- `τ₁ = (1 + 𝔞 − 2δ)/(αδ)` (40). -/
noncomputable def tau1 (𝔞 δ α : ℝ) : ℝ := (1 + 𝔞 - 2 * δ) / (α * δ)

/-- `τ₂ = 0 ∨ α⁻¹ log(r₀^{(1+𝔞)/(2δ)} (𝔡_𝔞 c₄)⁻¹)` (40). -/
noncomputable def tau2 (𝔞 δ α r₀ c₄ : ℝ) : ℝ :=
  max 0 (α⁻¹ * Real.log (r₀ ^ ((1 + 𝔞) / (2 * δ)) * (MLLangevin.General.da 𝔞 * c₄)⁻¹))

/-- `Υ₁² = 1 ∨ (α⁻²|b(x₀)|² + α⁻¹σ²d)` (12). -/
noncomputable def Upsilon1Sq (b : SDEState d → SDEState d) (σ α : ℝ) (x₀ : SDEState d) : ℝ :=
  max 1 (α⁻¹ ^ 2 * ‖b x₀‖ ^ 2 + α⁻¹ * σ ^ 2 * (d : ℝ))

/-- `β₁(x) = (L²/α)|x − x⋆|² + 2|b(x⋆)|²(1/α + L²/α³) + 3L²σ²d/α²` (Proposition 5.1 (i)). -/
noncomputable def beta1 (b : SDEState d → SDEState d) (σ α L : ℝ) (xs x : SDEState d) : ℝ :=
  L ^ 2 / α * ‖x - xs‖ ^ 2 + 2 * ‖b xs‖ ^ 2 * (1 / α + L ^ 2 / α ^ 3) +
    3 * L ^ 2 * σ ^ 2 * (d : ℝ) / α ^ 2

/-- `c₁(x) = |x − x⋆| + √(|b(x⋆)|²(1/L² + 2/α²) + 2σ²d/α)` (Lemma 5.1 (ii)). -/
noncomputable def c1fun (b : SDEState d → SDEState d) (σ α L : ℝ) (xs x : SDEState d) : ℝ :=
  ‖x - xs‖ + Real.sqrt (‖b xs‖ ^ 2 * (1 / L ^ 2 + 2 / α ^ 2) + 2 * σ ^ 2 * (d : ℝ) / α)

end MLLangevin.ConvexA1


