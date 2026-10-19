-- Prove2me | Definitions.Def_UnifErgHW_Diffusion_Lyapunov
-- name    : UnifErgHW_Diffusion_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:14.924685+00:00
-- url     : https://prove2.me/theorems/f82d4be5-dfd1-44dd-ace2-4d0ab684b4f1
-- title:
--   §2.1–§2.5, pp. 4–8 — centering (2.6), σ = diag(r), Markov controls, ψ_ε, Ψ_ε, Ψ, Ψ*_{ε,θ}, V (2.16), truncated drift b_c (2.14)
-- statement:
--   This module fixes the objects of the uniform exponential ergodicity theorem for the Halfin–Whitt limit of an $m$-class many-server queue.
--
--   The data are those of the published diffusion model: service rates $\mu_i>0$, abandonment rates $\gamma_i\ge 0$, diffusion coefficients $r_i>0$ and a constant vector $\ell\in\mathbb R^m$, for classes $i=1,\dots,m$. Write $e=(1,\dots,1)$, $M=\mathrm{diag}(\mu_i)$, $\Gamma=\mathrm{diag}(\gamma_i)$, and let $\Delta=\{u\in\mathbb R^m:u\ge 0,\ \langle e,u\rangle=1\}$ be the simplex of control values. The controlled drift is
--   $$
--   b(x,u)=\ell-M\big(x-\langle e,x\rangle^+u\big)-\langle e,x\rangle^+\Gamma u .
--   $$
--
--   The module defines:
--
--   1. **Centering** (Remark 2.3, (2.6)): $\ell=-\frac{\varrho}{m}Me$, i.e. $\ell_i=-\frac{\varrho}{m}\mu_i$, which ties the drift to the spare-capacity parameter $\varrho$.
--   2. **Normalization**: $\sum_i \frac{r_i^2}{2\mu_i}=1$, that is $\sum_i\tilde\lambda_i/\mu_i=1$ with $\tilde\lambda_i=r_i^2/2$.
--   3. The constant diffusion matrix $\sigma=\mathrm{diag}(r_1,\dots,r_m)$, so $a=\sigma\sigma^{\mathsf T}=\mathrm{diag}(r_i^2)=\mathrm{diag}(2\tilde\lambda_i)$.
--   4. The vector field $x\mapsto b(x,u)$ for a fixed control value $u$, and, for a map $v:\mathbb R^m\to\mathbb R^m$, the vector field $x\mapsto b(x,v(x))$.
--   5. **Stationary Markov controls** $\mathfrak U_{\mathrm{sm}}$: Borel measurable maps $v:\mathbb R^m\to\Delta$.
--   6. **Strong solutions and transition laws**: measurable solutions adapted to the Brownian filtration, and their common time-marginal laws under each Markov control.
--   7. $\|x\|_1=\sum_i|x_i|$ and $\|x^-\|_1=\sum_i\max(-x_i,0)$.
--   8. With the cut-off $\psi$ ($\psi=-\tfrac12$ on $(-\infty,-1]$, $\psi(t)=t$ on $[0,\infty)$) and $\varepsilon,\theta>0$:
--   $$
--   \psi_\varepsilon(t)=\psi(\varepsilon t),\quad \Psi_\varepsilon(x)=\sum_i\frac{\psi_\varepsilon(x_i)}{\mu_i},\quad \Psi(x)=\sum_i\frac{\psi(x_i)}{\mu_i},\quad \Psi^*_{\varepsilon,\theta}(x)=\varepsilon\theta\Psi(-x)+\Psi_\varepsilon(x),
--   $$
--   and the Lyapunov function $V(x)=\exp\big(\Psi^*_{\varepsilon,\theta}(x)\big)$ of (2.16).
--   9. For $c\in[1,\infty]$, the truncated drift (2.14)
--   $$
--   b^i_c(x,u)=-\frac{\varrho\mu_i}{m}-\mu_i\big(x_i-\langle e,x\rangle^+u_i\big)-\gamma_i\langle e,x\rangle^+u_i\,\mathbf 1_{\{x_i\le c\}} .
--   $$
--
--   These are the objects in terms of which Lemma 2.1 and Theorem 2.1 are stated; under the centering, $b_\infty=b$.
--
--   **Formalization Note** Classes are indexed by `Fin m` (class $i$ is index $i-1$). States live in `EuclideanSpace ℝ (Fin m)`, control values are vectors `Fin m → ℝ`, and $\Delta$ is Mathlib's `stdSimplex`. The parameter $c$ is an extended real with $c=\top$ standing for $c=\infty$. The cut-off $\psi$ is the published `GPhNGIDiffusion.EMError.cutoff`. The paper writes a state-dependent "covariance function" $\sigma(x)$ in (2.1), but its proof uses the constant $\sigma=\mathrm{diag}(2\tilde\lambda_i)^{1/2}$; that constant matrix is used here. The normalization is the identity $\sum_i\tilde\lambda_i/\mu_i=1$ that the proof of Theorem 2.1 uses in (2.31).
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, pp. 4–8, (2.1)–(2.2), p. 5 (𝔘sm), Remark 2.3 and (2.6) p. 7, Definition 2.2 and (2.9) p. 7, (2.14) and (2.16) p. 8, σ and (2.31) p. 10

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion

open Matrix
open MeasureTheory
open scoped NNReal

namespace UnifErgHW.Diffusion

/-!
Arapostathis, Hmedi, Pang, *On uniform exponential ergodicity of Markovian multiclass many-server
queues in the Halfin–Whitt regime*, arXiv:1812.03528v3, pp. 4–8, §2.1–§2.5: the objects of
Theorem 2.1 for the limiting controlled diffusion (2.1)

  `dX_t = b(X_t, U_t) dt + σ dW_t`,  `b(x, u) = ℓ − M(x − ⟨e,x⟩⁺u) − ⟨e,x⟩⁺Γu`  (2.2).

Formalization Note. Classes are `Fin m` (the paper's `i ∈ I = {1, …, m}` is index `i − 1`). The
state space is `EthierKurtz.SDEState m = EuclideanSpace ℝ (Fin m)`; a control value `u` is a vector
`Fin m → ℝ`, and the simplex `∆` is Mathlib's `stdSimplex ℝ (Fin m)`. The data `D` is the published
`ManyServerQED.Scheduling.DiffusionData m`: `D.mu i = µᵢ > 0`, `D.theta i = γᵢ ≥ 0` (the paper's
`Γ = diag(γᵢ)`), `D.r i > 0`, `D.ell = ℓ`; its `drift` is exactly (2.2). The covariance `σ` is the
constant diagonal matrix `diag(r)` (the proof of Theorem 2.1, p. 10, uses
`σ = diag(2λ̃₁, …, 2λ̃_m)^{1/2}`, so `λ̃ᵢ = rᵢ²/2` and `a = σσᵀ = diag(rᵢ²)`). The cut-off `ψ` of
p. 7 is the published `GPhNGIDiffusion.EMError.cutoff`.
-/

variable {m : ℕ}

/-- The centering of Remark 2.3 and (2.6), p. 7: `ℓ = −(ϱ/m) M e`, i.e. `ℓᵢ = −(ϱ/m) µᵢ` for every
class `i`. Then `ϱ = −⟨e, M⁻¹ℓ⟩` as in (2.3). -/
def IsCentered (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ : ℝ) : Prop :=
  ∀ i, D.ell i = -(ϱ / m) * D.mu i

/-- The normalization `∑ᵢ λ̃ᵢ/µᵢ = 1` used in the proof of Theorem 2.1 ((2.31), p. 10, "see (3.1)"),
with `λ̃ᵢ = rᵢ²/2`: `∑ᵢ rᵢ²/(2µᵢ) = 1`. -/
def IsNormalized (D : ManyServerQED.Scheduling.DiffusionData m) : Prop :=
  ∑ i, D.r i ^ 2 / (2 * D.mu i) = 1

/-- The constant diffusion matrix `σ = diag(r₁, …, r_m)` (p. 10). -/
noncomputable def sigma (D : ManyServerQED.Scheduling.DiffusionData m) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal D.r

/-- The drift `x ↦ b(x, u)` of (2.2) under the constant control value `u`, as a vector field on
`ℝ^m`. -/
noncomputable def ctrlDrift (D : ManyServerQED.Scheduling.DiffusionData m) (u : Fin m → ℝ) :
    EthierKurtz.SDEState m → EthierKurtz.SDEState m :=
  fun x => WithLp.toLp 2 (ManyServerQED.Scheduling.drift D (WithLp.ofLp x) u)

/-- `v ∈ 𝔘sm` (p. 5): `v` is a Borel measurable map `ℝ^m → ∆`. -/
def IsMarkovControl (v : EthierKurtz.SDEState m → Fin m → ℝ) : Prop :=
  Measurable v ∧ ∀ x, v x ∈ stdSimplex ℝ (Fin m)

/-- A solution is strong relative to its driving Brownian motion: at each time its value is,
almost surely, a measurable function of the Brownian path stopped at that time. -/
def IsStrongSolution {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
    (b : EthierKurtz.SDEState m → EthierKurtz.SDEState m)
    (σ : Matrix (Fin m) (Fin m) ℝ)
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState m) (x : EthierKurtz.SDEState m) : Prop :=
  GPhNGIDiffusion.EMError.SolvesAdditiveSDE b σ B X x ∧
    (∀ t, Measurable (X t)) ∧
    ∀ t : ℝ≥0, ∃ F : (ℝ≥0 → EthierKurtz.SDEState m) → EthierKurtz.SDEState m,
      Measurable F ∧ ∀ᵐ ω ∂Pr, X t ω = F (fun s => B (min s t) ω)

/-- The strong Feller property: at positive times the transition operator sends bounded Borel
functions to continuous functions. -/
def IsStrongFeller (P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m)) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ f : EthierKurtz.SDEState m → ℝ,
    Measurable f → Bornology.IsBounded (Set.range f) →
      Continuous (fun x => ∫ y, f y ∂(P t x))

/-- The drift `x ↦ b(x, v(x))` of (2.1) under the stationary Markov control `U_t = v(X_t)` (p. 5). -/
noncomputable def markovDrift (D : ManyServerQED.Scheduling.DiffusionData m)
    (v : EthierKurtz.SDEState m → Fin m → ℝ) :
    EthierKurtz.SDEState m → EthierKurtz.SDEState m :=
  fun x => WithLp.toLp 2 (ManyServerQED.Scheduling.drift D (WithLp.ofLp x) (v x))

/-- The transition probabilities of the strong SDE under a stationary Markov control: every
measurable strong solution has the same law at each time. -/
def IsMarkovTransition (D : ManyServerQED.Scheduling.DiffusionData m)
    (v : EthierKurtz.SDEState m → Fin m → ℝ)
    (P : ℝ≥0 → EthierKurtz.SDEState m → Measure (EthierKurtz.SDEState m)) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState m) (x : EthierKurtz.SDEState m),
    EthierKurtz.IsStandardBrownian Pr B →
    IsStrongSolution Pr (markovDrift D v) (sigma D) B X x →
    ∀ t, Pr.map (X t) = P t x

/-- `‖x‖₁ = ∑ᵢ |xᵢ|` (§1.1, p. 4). -/
def l1 (x : EthierKurtz.SDEState m) : ℝ :=
  ∑ i, |x i|

/-- `‖x⁻‖₁ = ∑ᵢ xᵢ⁻ = ∑ᵢ max(−xᵢ, 0)` (§1.1, p. 4). -/
def negL1 (x : EthierKurtz.SDEState m) : ℝ :=
  ∑ i, max (-(x i)) 0

/-- `ψ_ε(t) = ψ(εt)` (p. 7). -/
noncomputable def psiEps (ε t : ℝ) : ℝ :=
  GPhNGIDiffusion.EMError.cutoff (ε * t)

/-- `Ψ_ε(x) = ∑ᵢ ψ_ε(xᵢ)/µᵢ` ((2.9), p. 7). -/
noncomputable def PsiEps (D : ManyServerQED.Scheduling.DiffusionData m) (ε : ℝ)
    (x : EthierKurtz.SDEState m) : ℝ :=
  ∑ i, psiEps ε (x i) / D.mu i

/-- `Ψ(x) = ∑ᵢ ψ(xᵢ)/µᵢ` ((2.9), p. 7). -/
noncomputable def Psi (D : ManyServerQED.Scheduling.DiffusionData m)
    (x : EthierKurtz.SDEState m) : ℝ :=
  ∑ i, GPhNGIDiffusion.EMError.cutoff (x i) / D.mu i

/-- `Ψ*_{ε,θ}(x) = εθΨ(−x) + Ψ_ε(x)` ((2.9), p. 7). -/
noncomputable def PsiStar (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) : ℝ :=
  ε * θ * Psi D (-x) + PsiEps D ε x

/-- The Lyapunov function `V(x) = exp(Ψ*_{ε,θ}(x))` of (2.16), p. 8. -/
noncomputable def lyapV (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (x : EthierKurtz.SDEState m) : ℝ :=
  Real.exp (PsiStar D ε θ x)

/-- The truncated drift (2.14), p. 8, for `c ∈ [1, ∞]` (here `c : EReal`, `c = ⊤` being `∞`):
`b^i_c(x, u) = −ϱµᵢ/m − µᵢ(xᵢ − ⟨e,x⟩⁺uᵢ) − γᵢ⟨e,x⟩⁺uᵢ 1_{xᵢ ≤ c}`. -/
noncomputable def driftTrunc (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ : ℝ) (c : EReal)
    (x u : Fin m → ℝ) : Fin m → ℝ :=
  fun i => -(ϱ * D.mu i / m) - D.mu i * (x i - max (∑ j, x j) 0 * u i)
    - D.theta i * max (∑ j, x j) 0 * u i * (if ((x i : ℝ) : EReal) ≤ c then 1 else 0)

end UnifErgHW.Diffusion


