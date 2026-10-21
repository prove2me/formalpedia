-- Prove2me | Definitions.Def_SGHMCOpt_Euler_Model
-- name    : SGHMCOpt_Euler_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:24.184655+00:00
-- url     : https://prove2.me/theorems/968e0793-8abd-4d38-b08a-7c7f7521ead0
-- title:
--   §1–§2, pp. 2–10 — the stochastic program (1.1)–(1.2), Assumption 1, the Lyapunov function (2.1), the drift (2.2), SGHMC1 (1.8)–(1.9), the Gibbs law (1.7)
-- statement:
--   The model of Gao, Gürbüzbalaban and Zhu. A random loss $f:\mathbb R^d\times\mathcal Z\to\mathbb R$ and a population law $D$ on $\mathcal Z$ give the **population risk** and, for a dataset $z=(z_1,\dots,z_n)\in\mathcal Z^n$, the **empirical risk**
--   $$F(x)=\mathbb E_{Z\sim D}[f(x,Z)],\qquad F^*=\min_{x\in\mathbb R^d}F(x),\qquad F_z(x)=\frac1n\sum_{i=1}^nf(x,z_i).$$
--
--   1. **Assumption 1 (i)–(iii)** (`LossAssumption`): each $f(\cdot,\zeta)$ is $C^1$ and non-negative, $|f(0,\zeta)|\le A_0$, $\|\nabla f(0,\zeta)\|\le B$ with $A_0,B\ge0$; $\nabla f(\cdot,\zeta)$ is $M$-Lipschitz; and $\langle x,\nabla f(x,\zeta)\rangle\ge m\|x\|^2-b$, with $m,M>0$.
--   2. **Assumption 1 (iv)** (`OracleAssumption`): the stochastic gradient is $g(x,U)$ with $U$ of law $\nu_U$, unbiased, $\mathbb E\,g(x,U)=\nabla F_z(x)$, with $\mathbb E\|g(x,U)-\nabla F_z(x)\|^2\le2\delta(M^2\|x\|^2+B^2)$ for some $\delta\in[0,1)$.
--   3. **The Lyapunov function** (2.1): $\mathcal V(x,v)=\beta F_z(x)+\frac\beta4\gamma^2(\|x+\gamma^{-1}v\|^2+\|\gamma^{-1}v\|^2-\lambda\|x\|^2)$; **Assumption 1 (v)** (`InitAssumption`): $\int e^{\alpha\mathcal V}d\mu_0<\infty$ for every dataset, $\alpha=\lambda(1-2\lambda)/12$.
--   4. **The drift condition** (2.2) (`DriftCond`): $A>0$ and $x\cdot\nabla F_z(x)\ge2\lambda(F_z(x)+\gamma^2\|x\|^2/4)-2A/\beta$ for all $z$ and $x$.
--   5. **SGHMC1** (1.8)–(1.9): from $(X_0,V_0)\sim\mu_0$,
--   $$V_{k+1}=V_k-\eta[\gamma V_k+g(X_k,U_{z,k})]+\sqrt{2\gamma\beta^{-1}\eta}\,\xi_k,\qquad X_{k+1}=X_k+\eta V_k,$$
--   with $\xi_k$ i.i.d. standard Gaussian in $\mathbb R^d$ and $U_{z,k}$ i.i.d. of law $\nu_U$, all independent of each other and of $(X_0,V_0)$ (`SGHMC1Noise`). The law of $(X_k,V_k)$ is $\mu_{k,z}$.
--   6. **The Gibbs law** (1.7): $\pi_z(dx,dv)=\Gamma_z^{-1}\exp(-\beta(\frac12\|v\|^2+F_z(x)))\,dx\,dv$, and its $x$-marginal.
--   7. **Spectral gap** (`HasPoincare`): $\lambda_0$ satisfies $\lambda_0\int\varphi^2d\pi_z\le\beta^{-1}\int\|\nabla\varphi\|^2d\pi_z$ for every $z$ and every $\varphi\in C^1(\mathbb R^d)\cap L^2(\pi_z)$ with $\int\varphi\,d\pi_z=0$ ($\pi_z$ the $x$-marginal), i.e. $\lambda_0\le\lambda_*$ of (3.8).
--
--   SGHMC1 is the Euler discretisation of underdamped Langevin dynamics, whose invariant law is $\pi_z$; every result of the mission compares $\mu_{k,z}$ with $\pi_z$ and $\pi_z$ with the minimisers of $F$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; the phase space is the product $\mathbb R^d\times\mathbb R^d$, and every Euclidean norm on it is written $\|x\|^2+\|v\|^2$. The oracle is a function $g(z,x,u)$ of the dataset, the point and an oracle draw $u$ whose law $\nu_U$ does not depend on $z$; this covers minibatch sampling. Independence is the mutual independence of the σ-algebras of $(X_0,V_0)$, of each $\xi_k$ and of each $U_k$. $f$ is jointly measurable and $g$ is jointly measurable in $(z,x,u)$; this is the standing convention that makes $F$, the laws $\mu_{k,z}$ and the outer expectation over the sample genuine (a non-measurable map would have the zero measure as its law in Lean). The variance bound uses a lower Lebesgue integral. $F^*$ is the infimum of $F\ge0$; it is attained under Assumption 1. $\Gamma_z$ is computed in $[0,\infty]$ against Lebesgue measure on $\mathbb R^d\times\mathbb R^d$. The spectral-gap condition compares a real left side with an $[0,\infty]$-valued Dirichlet energy, so a test function of infinite energy imposes nothing, as in the paper's infimum of ratios.
-- source:
--   arXiv:1809.04618v4, (1.1), (1.2), p. 2; (1.7), (1.8), (1.9), p. 4; Assumption 1, pp. 9–10; (2.1), (2.2), p. 10; (3.8), p. 12; x-marginal of π_z, p. 41

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants

open MeasureTheory ProbabilityTheory

namespace SGHMCOpt.Euler

/-- The decision space `ℝ^d` with its Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d n : ℕ} {𝒵 𝒰 : Type*}

/-- The empirical risk `F_z(x) = (1/n) Σᵢ f(x, zᵢ)` (1.2) of the dataset `z = (z₁, …, zₙ)`. -/
noncomputable def Fz (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵) (x : E d) : ℝ :=
  1 / (n : ℝ) * ∑ i, f x (z i)

/-- The population risk `F(x) = E_{Z∼D}[f(x, Z)]` (1.1). -/
noncomputable def F [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (D : Measure 𝒵) (x : E d) : ℝ :=
  ∫ ζ, f x ζ ∂D

/-- The minimum value `F* = min_{x ∈ ℝ^d} F(x)` (p. 2), written as an infimum. -/
noncomputable def Fstar [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (D : Measure 𝒵) : ℝ :=
  ⨅ x, F f D x

/-- The Lyapunov function (2.1):
`𝒱(x, v) = βF_z(x) + (β/4)γ²(‖x + γ⁻¹v‖² + ‖γ⁻¹v‖² − λ‖x‖²)`. -/
noncomputable def lyap (p : Params) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵) (x v : E d) : ℝ :=
  p.β * Fz f z x +
    p.β / 4 * p.γ ^ 2 * (‖x + p.γ⁻¹ • v‖ ^ 2 + ‖p.γ⁻¹ • v‖ ^ 2 - p.lam * ‖x‖ ^ 2)

/-- Assumption 1 (i)–(iii), p. 9, together with the joint measurability of `f` (so that the
population risk `F` is a genuine integral):
(i) `f(·, ζ)` is continuously differentiable and non-negative, `A₀, B ≥ 0`, `|f(0, ζ)| ≤ A₀` and
`‖∇f(0, ζ)‖ ≤ B`; (ii) `∇f(·, ζ)` is `M`-Lipschitz; (iii) `⟨x, ∇f(x, ζ)⟩ ≥ m‖x‖² − b`.
The constants `m` and `M` are positive. -/
structure LossAssumption [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (p : Params) : Prop where
  measurable : Measurable (Function.uncurry f)
  contDiff : ∀ ζ, ContDiff ℝ 1 (fun x => f x ζ)
  nonneg : ∀ x ζ, 0 ≤ f x ζ
  A0_nonneg : 0 ≤ p.A0
  B_nonneg : 0 ≤ p.B
  bound_zero : ∀ ζ, |f 0 ζ| ≤ p.A0
  grad_zero : ∀ ζ, ‖gradient (fun x => f x ζ) 0‖ ≤ p.B
  M_pos : 0 < p.M
  smooth : ∀ ζ w v,
    ‖gradient (fun x => f x ζ) w - gradient (fun x => f x ζ) v‖ ≤ p.M * ‖w - v‖
  m_pos : 0 < p.m
  dissipative : ∀ ζ x, p.m * ‖x‖ ^ 2 - p.b ≤ inner ℝ x (gradient (fun x => f x ζ) x)

/-- Assumption 1 (iv), p. 9, with the unbiasedness of the gradient oracle (p. 4). The oracle is
`g z x u`: for the dataset `z` and the point `x` it returns `g(x, u)`, where the randomness `u`
has law `νU`. Required: `g` jointly measurable; `δ ∈ [0, 1)`; `E g(x, U) = ∇F_z(x)`; and
`E‖g(x, U) − ∇F_z(x)‖² ≤ 2δ(M²‖x‖² + B²)` for every `z` and `x`. -/
structure OracleAssumption [MeasurableSpace 𝒵] [MeasurableSpace 𝒰] (f : E d → 𝒵 → ℝ)
    (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰) (p : Params) : Prop where
  measurable : Measurable (fun q : (Fin n → 𝒵) × E d × 𝒰 => g q.1 q.2.1 q.2.2)
  δ_mem : 0 ≤ p.δ ∧ p.δ < 1
  unbiased : ∀ z x, Integrable (g z x) νU ∧ ∫ u, g z x u ∂νU = gradient (Fz f z) x
  variance : ∀ z x, ∫⁻ u, ENNReal.ofReal (‖g z x u - gradient (Fz f z) x‖ ^ 2) ∂νU ≤
    ENNReal.ofReal (2 * p.δ * (p.M ^ 2 * ‖x‖ ^ 2 + p.B ^ 2))

/-- Assumption 1 (v), p. 10: `∫ e^{α𝒱(x,v)} μ₀(dx, dv) < ∞`, with `α = λ(1 − 2λ)/12`, for the
Lyapunov function of every dataset `z ∈ 𝒵ⁿ`. -/
def InitAssumption (n : ℕ) (f : E d → 𝒵 → ℝ) (μ0 : Measure (E d × E d)) (p : Params) : Prop :=
  ∀ z : Fin n → 𝒵, ∫⁻ q, ENNReal.ofReal (Real.exp (alpha p * lyap p f z q.1 q.2)) ∂μ0 < ⊤

/-- The drift condition (2.2), p. 10: `A > 0` and, for every dataset `z` and every `x`,
`x · ∇F_z(x) ≥ 2λ(F_z(x) + γ²‖x‖²/4) − 2A/β`. -/
def DriftCond (n : ℕ) (f : E d → 𝒵 → ℝ) (p : Params) : Prop :=
  0 < p.A ∧ ∀ (z : Fin n → 𝒵) (x : E d),
    2 * p.lam * (Fz f z x + p.γ ^ 2 * ‖x‖ ^ 2 / 4) - 2 * p.A / p.β ≤
      inner ℝ x (gradient (Fz f z) x)

/-- The SGHMC1 iterates (1.8)–(1.9), p. 4, from `(X₀, V₀)`:
`V_{k+1} = V_k − η[γV_k + g(X_k, U_{z,k})] + √(2γβ⁻¹η) ξ_k`, `X_{k+1} = X_k + ηV_k`.
The value at step `k` and outcome `ω` is the pair `(X_k(ω), V_k(ω))`. -/
noncomputable def sghmc1 {Ω : Type*} (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (z : Fin n → 𝒵)
    (p : Params) (η : ℝ) (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d) (U : ℕ → Ω → 𝒰) :
    ℕ → Ω → E d × E d
  | 0 => fun ω => (X0 ω, V0 ω)
  | k + 1 => fun ω =>
      ((sghmc1 g z p η X0 V0 ξ U k ω).1 + η • (sghmc1 g z p η X0 V0 ξ U k ω).2,
       (sghmc1 g z p η X0 V0 ξ U k ω).2 -
          η • (p.γ • (sghmc1 g z p η X0 V0 ξ U k ω).2 +
            g z (sghmc1 g z p η X0 V0 ξ U k ω).1 (U k ω)) +
        Real.sqrt (2 * p.γ * p.β⁻¹ * η) • ξ k ω)

set_option warn.classDefReducibility false in
/-- The σ-algebras generated by the initial state `(X₀, V₀)` (index `none`), by each Gaussian
vector `ξ_k` (index `some (inl k)`) and by each oracle draw `U_k` (index `some (inr k)`). -/
def noiseSigma [MeasurableSpace 𝒰] {Ω : Type*} (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d)
    (U : ℕ → Ω → 𝒰) : Option (ℕ ⊕ ℕ) → MeasurableSpace Ω
  | none => MeasurableSpace.comap (fun ω => (X0 ω, V0 ω)) inferInstance
  | some (Sum.inl k) => MeasurableSpace.comap (ξ k) inferInstance
  | some (Sum.inr k) => MeasurableSpace.comap (U k) inferInstance

/-- The randomness of SGHMC1 (p. 4 and Theorem 2): on the probability space `(Ω, P)`, the initial
state `(X₀, V₀)` has law `μ₀`, the `ξ_k` are standard Gaussian vectors in `ℝ^d`, the `U_k` have the
common law `νU`, and `(X₀, V₀), ξ₀, ξ₁, …, U₀, U₁, …` are mutually independent and measurable. -/
structure SGHMC1Noise [MeasurableSpace 𝒰] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d) (U : ℕ → Ω → 𝒰) (μ0 : Measure (E d × E d))
    (νU : Measure 𝒰) : Prop where
  isProb : IsProbabilityMeasure P
  meas_init : Measurable (fun ω => (X0 ω, V0 ω))
  meas_ξ : ∀ k, Measurable (ξ k)
  meas_U : ∀ k, Measurable (U k)
  law_init : P.map (fun ω => (X0 ω, V0 ω)) = μ0
  law_ξ : ∀ k, P.map (ξ k) = stdGaussian (E d)
  law_U : ∀ k, P.map (U k) = νU
  indep : iIndep (noiseSigma X0 V0 ξ U) P

/-- The law `μ_{k,z}` of the SGHMC1 iterate `(X_k, V_k)` for the dataset `z` (p. 10). -/
noncomputable def lawSGHMC1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (z : Fin n → 𝒵) (p : Params) (η : ℝ)
    (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d) (U : ℕ → Ω → 𝒰) (k : ℕ) : Measure (E d × E d) :=
  P.map (sghmc1 g z p η X0 V0 ξ U k)

/-- The unnormalised Gibbs density `exp(−β(‖v‖²/2 + F_z(x)))` of (1.7). -/
noncomputable def gibbsDensity (p : Params) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵)
    (q : E d × E d) : ENNReal :=
  ENNReal.ofReal (Real.exp (-p.β * (‖q.2‖ ^ 2 / 2 + Fz f z q.1)))

/-- The normalising constant `Γ_z = ∫ exp(−β(‖v‖²/2 + F_z(x))) dx dv` of (1.7). -/
noncomputable def gibbsNorm (p : Params) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵) : ENNReal :=
  ∫⁻ q, gibbsDensity p f z q ∂((volume : Measure (E d)).prod (volume : Measure (E d)))

/-- The Gibbs law (1.7), p. 4: `π_z(dx, dv) = Γ_z⁻¹ exp(−β(‖v‖²/2 + F_z(x))) dx dv`. -/
noncomputable def gibbs (p : Params) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵) : Measure (E d × E d) :=
  (gibbsNorm p f z)⁻¹ •
    ((volume : Measure (E d)).prod (volume : Measure (E d))).withDensity (gibbsDensity p f z)

/-- The `x`-marginal of `π_z` (p. 41: `π_z(dx) = Λ_z e^{−βF_z(x)} dx`). -/
noncomputable def gibbsX (p : Params) (f : E d → 𝒵 → ℝ) (z : Fin n → 𝒵) : Measure (E d) :=
  (gibbs p f z).map Prod.fst

/-- `λ₀` is a lower bound of the uniform spectral gap `λ_*` of (3.8), p. 12: for every dataset
`z ∈ 𝒵ⁿ` and every `φ ∈ C¹(ℝ^d) ∩ L²(π_z)` with `∫ φ dπ_z = 0`,
`λ₀ ∫ φ² dπ_z ≤ β⁻¹ ∫ ‖∇φ‖² dπ_z` (the right side may be `+∞`). Here `π_z` is the `x`-marginal. -/
def HasPoincare (n : ℕ) (f : E d → 𝒵 → ℝ) (p : Params) (lam0 : ℝ) : Prop :=
  ∀ z : Fin n → 𝒵, ∀ φ : E d → ℝ, ContDiff ℝ 1 φ → MemLp φ 2 (gibbsX p f z) →
    ∫ x, φ x ∂(gibbsX p f z) = 0 →
    ENNReal.ofReal (lam0 * ∫ x, φ x ^ 2 ∂(gibbsX p f z)) ≤
      ENNReal.ofReal p.β⁻¹ * ∫⁻ x, ENNReal.ofReal (‖gradient φ x‖ ^ 2) ∂(gibbsX p f z)

end SGHMCOpt.Euler


