-- Prove2me | Definitions.Def_NonconvexAG_Stoch_RSAG
-- name    : NonconvexAG_Stoch_RSAG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:21:26.185783+00:00
-- url     : https://prove2.me/theorems/f3ddcb08-3019-471e-9222-2c92869ad9dd
-- title:
--   Algorithm 3 — the randomized stochastic AG (RSAG) run, Γ_k (2.6), C_k (2.7), the mass functions (3.4) and (3.7)
-- statement:
--   This file fixes the objects of §3.1 of Ghadimi and Lan: the randomized stochastic accelerated gradient (RSAG) method for $\Psi^*=\min_{x\in\mathbb R^n}\Psi(x)$ when only a stochastic first-order oracle is available, its weights $\Gamma_k$, the constants $C_k$, and the two probability mass functions of the random termination index.
--
--   **Oracle and noise.** $(\Omega,\mathcal F,\mu)$ is a probability space, $\Xi$ a measurable noise space, $G:\mathbb R^n\times\Xi\to\mathbb R^n$ the stochastic oracle and $\xi_1,\xi_2,\dots:\Omega\to\Xi$ the noise variables; at its $k$-th call at the input $x$ the oracle returns $G(x,\xi_k)$.
--
--   **Step sizes.** Sequences $\{\alpha_k\},\{\beta_k\},\{\lambda_k\}$ ($k\ge1$) with
--   $$\alpha_1=1,\qquad \alpha_k\in(0,1)\ (k\ge2),\qquad \beta_k>0,\qquad \lambda_k>0 .$$
--
--   **The run (Algorithm 3).** From $x_0\in\mathbb R^n$, set $x^{ag}_0=x_0$ and, for $k=1,2,\dots$, pointwise on $\Omega$,
--   $$x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_k x_{k-1},\qquad x_k=x_{k-1}-\lambda_k G(x^{md}_k,\xi_k),\qquad x^{ag}_k=x^{md}_k-\beta_k G(x^{md}_k,\xi_k),$$
--   which are (2.2), (3.2) and (3.3). The **oracle error** is $\delta_k=G(x^{md}_k,\xi_k)-\nabla\Psi(x^{md}_k)$.
--
--   **Weights (2.6) and constants (2.7).** $\Gamma_1=1$, $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$, that is $\Gamma_k=\prod_{i=2}^k(1-\alpha_i)$; for a horizon $N$ and $1\le k\le N$,
--   $$C_k=1-L_\Psi\lambda_k-\frac{L_\Psi(\lambda_k-\beta_k)^2}{2\alpha_k\Gamma_k\lambda_k}\Big(\sum_{\tau=k}^N\Gamma_\tau\Big).$$
--
--   **Mass functions.** For $k=1,\dots,N$,
--   $$p_k=\frac{\lambda_kC_k}{\sum_{j=1}^N\lambda_jC_j}\quad(3.4),\qquad p_k=\frac{\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)}{\sum_{j=1}^N\Gamma_j^{-1}\beta_j(1-L_\Psi\beta_j)}\quad(3.7).$$
--
--   **Termination index (3.1).** A random variable $R:\Omega\to\mathbb N$ that is measurable, takes values in $\{1,\dots,N\}$, and satisfies $\Pr\{R=k\}=p_k$ for $k=1,\dots,N$. The output of the method is $(x^{md}_R,x^{ag}_R)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`, the published `GhadimiLan.RSG.E n`. The run is defined along a single noise realization (`rsagPath`, by recursion on $k$) and evaluated at $\omega$, so `xSeq`, `xagSeq`, `xmdSeq` are $x_k$, $x^{ag}_k$, $x^{md}_k$ as random vectors, and `delta` is $\delta_k$. The iterates are defined for every $k$; the paper's "terminate at $k=R$" is the equivalent "run $N$ iterations and output the $R$-th pair" the paper itself describes on p. 15. Step sizes are functions `ℕ → ℝ` indexed from 1; their values at index 0 carry no hypothesis and `xmdSeq` at index 0 is a junk value never used. $\Gamma$ is the product over $\{2,\dots,k\}$, so $\Gamma_1=1$. $C_k$ depends on $N$ and is `C LΨ α β lam N k`; `lam` is $\lambda$. `IsOutputIndex μ R N p` records (3.1) for a given mass function `p` (applied to `pmfA` for (3.4) and `pmfB` for (3.7)); the independence of $R$ from the noise is a separate hypothesis of every theorem that uses $R$. Assumption 1 is the published `GhadimiLan.RSG.AssumptionA1`, applied to the trajectory of middle points $x^{md}_k$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, (2.2) and (2.6); p. 5, (2.7); p. 15, Algorithm 3 (3.1)–(3.3), Theorem 3 (3.4) and (3.7)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Smooth_AGRun

open MeasureTheory ProbabilityTheory

namespace NonconvexAG.Stoch

open GhadimiLan.RSG (E)

/-- The input conditions of Algorithm 3 (Ghadimi–Lan, arXiv:1310.3787v1, p. 15), identical to
those of Algorithm 1 (p. 4): `α₁ = 1`, `αₖ ∈ (0, 1)` for `k ≥ 2`, `βₖ > 0` and `λₖ > 0` for
`k ≥ 1`. Indexing is 1-based as in the paper; the values at index `0` carry no hypothesis. -/
def RSAGStepsizes (α β lam : ℕ → ℝ) : Prop :=
  α 1 = 1 ∧ (∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) ∧ (∀ k, 1 ≤ k → 0 < β k) ∧
    ∀ k, 1 ≤ k → 0 < lam k

/-- The RSAG recursion of Algorithm 3 (p. 15) along one realization `s : ℕ → Ξ` of the noise
`(ξ₁, ξ₂, …)`, with stochastic oracle `G`, step sizes `α, β, λ` and start `x₀`: the pair
`(xₖ, x^ag_k)`. At `k = 0` both equal `x₀` (step 0: `x^ag_0 = x_0 = x₀`); for `k ≥ 1`, with
`x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` (2.2),
`xₖ = x_{k−1} − λₖ G(x^md_k, ξₖ)` (3.2) and `x^ag_k = x^md_k − βₖ G(x^md_k, ξₖ)` (3.3). -/
def rsagPath {n : ℕ} {Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (s : ℕ → Ξ) : ℕ → E n × E n
  | 0 => (x0, x0)
  | k + 1 =>
    let p := rsagPath G α β lam x0 s k
    let md := (1 - α (k + 1)) • p.2 + α (k + 1) • p.1
    let Gk := G md (s (k + 1))
    (p.1 - lam (k + 1) • Gk, md - β (k + 1) • Gk)

/-- The iterate `xₖ` of Algorithm 3 as a random vector on `Ω`, for noise variables `ξ k : Ω → Ξ`. -/
def xSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (rsagPath G α β lam x0 (fun j => ξ j ω) k).1

/-- The aggregated iterate `x^ag_k` of Algorithm 3 as a random vector on `Ω`. -/
def xagSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (rsagPath G α β lam x0 (fun j => ξ j ω) k).2

/-- The middle iterate `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` of (2.2), meaningful for
`k ≥ 1` (at the unused index `0` it is a junk value). -/
def xmdSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (α β lam : ℕ → ℝ) (x0 : E n)
    (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (1 - α k) • xagSeq G α β lam x0 ξ (k - 1) ω + α k • xSeq G α β lam x0 ξ (k - 1) ω

/-- The oracle error `δₖ = G(x^md_k, ξₖ) − ∇Ψ(x^md_k)` (proof of Theorem 3, p. 16), with `g`
the gradient map `∇Ψ`. -/
def delta {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (g : E n → E n) (α β lam : ℕ → ℝ)
    (x0 : E n) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  G (xmdSeq G α β lam x0 ξ k ω) (ξ k ω) - g (xmdSeq G α β lam x0 ξ k ω)

/-- The probability mass function (3.4) of Theorem 3 a), p. 15:
`pₖ = λₖ Cₖ / Σ_{j=1}^{N} λⱼ Cⱼ`, for `k = 1, …, N`. -/
noncomputable def pmfA (LΨ : ℝ) (α β lam : ℕ → ℝ) (N k : ℕ) : ℝ :=
  lam k * NonconvexAG.Smooth.C LΨ α β lam N k / ∑ j ∈ Finset.Icc 1 N, lam j * NonconvexAG.Smooth.C LΨ α β lam N j

/-- The probability mass function (3.7) of Theorem 3 b), p. 15:
`pₖ = Γₖ⁻¹ βₖ (1 − L_Ψ βₖ) / Σ_{j=1}^{N} Γⱼ⁻¹ βⱼ (1 − L_Ψ βⱼ)`, for `k = 1, …, N`. -/
noncomputable def pmfB (LΨ : ℝ) (α β : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) /
    ∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j)

/-- The random termination index `R` of Algorithm 3 (step 0 and (3.1), p. 15): `R : Ω → ℕ` is
measurable, takes values in `{1, …, N}`, and `Prob{R = k} = p k` for `k = 1, …, N`.
Independence of `R` from the noise is a separate hypothesis of the theorems that use `R`. -/
def IsOutputIndex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ℕ) (N : ℕ)
    (p : ℕ → ℝ) : Prop :=
  Measurable R ∧ (∀ ω, R ω ∈ Finset.Icc 1 N) ∧
    ∀ k ∈ Finset.Icc 1 N, μ {ω | R ω = k} = ENNReal.ofReal (p k)

end NonconvexAG.Stoch


