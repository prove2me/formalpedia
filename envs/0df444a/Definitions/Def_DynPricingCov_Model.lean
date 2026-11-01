-- Prove2me | Definitions.Def_DynPricingCov_Model
-- name    : DynPricingCov_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:00.526091+00:00
-- url     : https://prove2.me/theorems/9687c183-e966-43c0-b0f1-d4661381e200
-- title:
--   The generalized linear demand model with covariates: Assumptions 1–3, revenue $r$, $r^*$, design matrix $M_t$, regret
-- statement:
--   A seller prices one product over periods $t=1,\dots,T$. In period $t$ it observes a covariate vector $x_t\in\mathcal X\subseteq\mathbb R^d$, sets a price $p_t$, and observes the demand
--
--   $$
--   D_t=g(x_t^\top\alpha^*+x_t^\top\beta^*\cdot p_t)+\epsilon_t ,\qquad (1)
--   $$
--
--   with a known link function $g$, unknown parameter $\theta^*=(\alpha^*,\beta^*)\in\mathbb R^{2d}$ and demand shock $\epsilon_t$. The **regressor** is $z_t=(x_t,p_tx_t)\in\mathbb R^{2d}$, so $z_t^\top\theta=x_t^\top\alpha+x_t^\top\beta\cdot p_t$.
--
--   1. **Assumption 1 (Boundedness).** (a) $\bar\theta>0$ and $\theta^*\in\Theta=\{\theta\in\mathbb R^{2d}:\|\theta\|_2\le\bar\theta\}$; (b) prices lie in $[\underline p,\bar p]$; (c) a known $\bar D>0$ bounds $g(x^\top\alpha^*+x^\top\beta^*p)$ for all $x\in\mathcal X$, $p\in[\underline p,\bar p]$; (d) $\|(x,px)\|_2\le1$ for all such $x,p$.
--   2. **Assumption 2.** $g$ is strictly increasing and differentiable, with $0<\underline g\le g'(u)\le\bar g$ for every $u$ in $Z=\{x^\top\alpha+x^\top\beta\cdot p: x\in\mathcal X,\ \theta\in\Theta,\ p\in[\underline p,\bar p]\}$.
--   3. **Assumption 3.** $\{\epsilon_t\}$ is a $\bar\sigma^2$-sub-Gaussian martingale difference sequence: $\mathbb E[\epsilon_t\mid\mathcal H_{t-1}]=0$ and $\log\mathbb E[e^{s\epsilon_t}\mid\mathcal H_{t-1}]\le\bar\sigma^2s^2/2$ for all $s\in\mathbb R$.
--
--   The **expected revenue** is $r(p;a,b)=p\cdot g(a+b\,p)$ and the **optimal expected revenue** is $r^*(a,b)=\max_{p\in[\underline p,\bar p]}p\cdot g(a+b\,p)$. The **design matrix** is $M_t=\lambda I_{2d}+\sum_{t'=1}^t z_{t'}z_{t'}^\top$ and the $M$-norm is $\|v\|_M=\sqrt{v^\top Mv}$. With $a_t^*=x_t^\top\alpha^*$, $b_t^*=x_t^\top\beta^*$ and the realized revenue $p_tD_t$, the **regret** of a pricing policy is
--
--   $$
--   \mathrm{Reg}_T(x_1,\dots,x_T)=\sum_{t=1}^T r^*(a_t^*,b_t^*)-\mathbb E\Big[\sum_{t=1}^T p_tD_t\Big].
--   $$
--
--   The covariates are an arbitrary deterministic sequence: no expectation is taken over them. These objects are shared by every statement of the mission.
--
--   **Formalization Note** Vectors of $\mathbb R^{2d}$ are `Fin (d + d) → ℝ`, with $\theta$ = `Fin.append α β` and $z(x,p)$ = `Fin.append x (p • x)`. Assumption 1(b) is a condition on the price process and is stated with it. The filtration $\mathcal F$ is arbitrary (the paper's $\mathcal H$ is one): the shock of period $t+1$ is $\mathcal F_{t+1}$-measurable and conditioned on $\mathcal F_t$, and the sub-Gaussian condition is Mathlib's `HasCondSubgaussianMGF` with variance proxy $\bar\sigma^2$, which needs a standard Borel sample space; $\bar\sigma>0$. $r^*$ is the supremum over $[\underline p,\bar p]$, attained for continuous $g$. $M_t$ is the published `BanditAlgorithm.regularizedDesignMatrix`. The expectation is the Bochner integral.
-- source:
--   Wang, Talluri & Li, On Dynamic Pricing with Covariates, arXiv:2112.13254v3, §2, (1), Assumptions 1–3, pp.4–5; §3.1, design matrix and M-norm, p.6; Appendix C.1.1, ξₜ(θ), p.25

import Mathlib
import Definitions.Def_SelfNormalizedProcess

open MeasureTheory ProbabilityTheory Matrix

namespace DynPricingCov

/-- The first half `α` of a parameter vector `θ = (α, β) ∈ ℝ^{2d}`, Wang, Talluri & Li, On Dynamic
Pricing with Covariates, arXiv:2112.13254v3, §2, p.4 ("θ* := (α*, β*) as the concatenated true
parameter vector").

**Formalization Note** Vectors of `ℝ^{2d}` are `Fin (d + d) → ℝ`, and `θ = Fin.append α β`; the first
`d` coordinates are `α`. -/
def alphaOf {d : ℕ} (θ : Fin (d + d) → ℝ) : Fin d → ℝ := fun i => θ (Fin.castAdd d i)

/-- The second half `β` of a parameter vector `θ = (α, β) ∈ ℝ^{2d}` (arXiv:2112.13254v3, p.4). -/
def betaOf {d : ℕ} (θ : Fin (d + d) → ℝ) : Fin d → ℝ := fun i => θ (Fin.natAdd d i)

/-- The regressor `z = (x, p x) ∈ ℝ^{2d}` of covariate `x` at price `p`, arXiv:2112.13254v3, §3.1,
p.5 ("z_t = (x_t, p_t x_t) is a column vector by concatenating the covariates"). Its inner product
with `θ = (α, β)` is `xᵀα + xᵀβ · p`. -/
def z {d : ℕ} (x : Fin d → ℝ) (p : ℝ) : Fin (d + d) → ℝ := Fin.append x (p • x)

/-- The parameter set `Θ = {θ ∈ ℝ^{2d} : ‖θ‖₂ ≤ θ̄}`, arXiv:2112.13254v3, Assumption 1(a), p.4. -/
def Theta (d : ℕ) (θbar : ℝ) : Set (Fin (d + d) → ℝ) := {θ | Real.sqrt (θ ⬝ᵥ θ) ≤ θbar}

/-- The set `Z = {xᵀα + xᵀβ · p : x ∈ 𝒳, θ = (α, β) ∈ Θ, p ∈ [p̲, p̄]}` on which Assumption 2
(arXiv:2112.13254v3, p.4) bounds the derivative of the link function. -/
def Zset {d : ℕ} (X : Set (Fin d → ℝ)) (θbar plo phi : ℝ) : Set ℝ :=
  {u | ∃ x ∈ X, ∃ θ ∈ Theta d θbar, ∃ p ∈ Set.Icc plo phi,
    u = x ⬝ᵥ alphaOf θ + (x ⬝ᵥ betaOf θ) * p}

/-- The expected revenue function `r(p; a, b) = p · g(a + b · p)`, arXiv:2112.13254v3, §2, p.4. -/
def r (g : ℝ → ℝ) (p a b : ℝ) : ℝ := p * g (a + b * p)

/-- The optimal expected revenue `r*(a, b) = max_{p ∈ [p̲, p̄]} p · g(a + b · p)`,
arXiv:2112.13254v3, §2, p.5.

**Formalization Note** Written as `sSup` of the revenue over `[p̲, p̄]`. For a continuous `g` (as
under Assumption 2) and `p̲ ≤ p̄` the supremum is attained, so it is the paper's maximum. -/
noncomputable def rstar (g : ℝ → ℝ) (plo phi a b : ℝ) : ℝ :=
  sSup ((fun q => r g q a b) '' Set.Icc plo phi)

/-- The `M`-norm `‖v‖_M = √(vᵀ M v)`, arXiv:2112.13254v3, §3.1, p.6. -/
noncomputable def mNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ M *ᵥ v)

/-- **Assumption 1 (Boundedness)**, arXiv:2112.13254v3, p.4, parts (a), (c), (d):
(a) `θ̄ > 0` and `θ* ∈ Θ`; (c) a known `D̄ > 0` with `g(xᵀα* + xᵀβ* · p) ≤ D̄` for all `x ∈ 𝒳`,
`p ∈ [p̲, p̄]`; (d) `‖(x, px)‖₂ ≤ 1` for all `x ∈ 𝒳`, `p ∈ [p̲, p̄]`.

**Formalization Note** Part (b), "the seller sets prices in a range `[p̲, p̄]`", is a condition on
the price process and is stated with it (in the run predicate or the admissible-price hypothesis). -/
structure Assumption1 {d : ℕ} (X : Set (Fin d → ℝ)) (θbar plo phi Dbar : ℝ) (g : ℝ → ℝ)
    (θstar : Fin (d + d) → ℝ) : Prop where
  /-- (a) `θ̄ > 0`. -/
  θbar_pos : 0 < θbar
  /-- (a) `θ* ∈ Θ`. -/
  θstar_mem : θstar ∈ Theta d θbar
  /-- (c) `D̄ > 0`. -/
  Dbar_pos : 0 < Dbar
  /-- (c) the mean demand is at most `D̄`. -/
  demand_le : ∀ x ∈ X, ∀ p ∈ Set.Icc plo phi,
    g (x ⬝ᵥ alphaOf θstar + (x ⬝ᵥ betaOf θstar) * p) ≤ Dbar
  /-- (d) `‖(x, px)‖₂ ≤ 1`. -/
  z_norm_le : ∀ x ∈ X, ∀ p ∈ Set.Icc plo phi, Real.sqrt (z x p ⬝ᵥ z x p) ≤ 1

/-- **Assumption 2 (Properties of `g`)**, arXiv:2112.13254v3, p.4: `g` is strictly increasing and
differentiable, and there are constants `0 < g̲ ≤ g′(u) ≤ ḡ` for all `u = xᵀα + xᵀβ · p` with
`x ∈ 𝒳`, `θ ∈ Θ`, `p ∈ [p̲, p̄]`.

**Formalization Note** The derivative bounds are required on `Z` only (the "Specifically" clause of
Assumption 2); no global bound on `g′` is assumed. -/
structure Assumption2 {d : ℕ} (X : Set (Fin d → ℝ)) (θbar plo phi glo ghi : ℝ) (g : ℝ → ℝ) :
    Prop where
  strictMono : StrictMono g
  differentiable : Differentiable ℝ g
  glo_pos : 0 < glo
  deriv_mem : ∀ u ∈ Zset X θbar plo phi, glo ≤ deriv g u ∧ deriv g u ≤ ghi

/-- **Assumption 3 (Demand Shock)**, arXiv:2112.13254v3, p.4: `{ε_t}` is a `σ̄²`-sub-Gaussian
martingale difference sequence, `E[ε_t | ℋ_{t−1}] = 0` and `log E[e^{sε_t} | ℋ_{t−1}] ≤ σ̄²s²/2`
for all `s ∈ ℝ`.

**Formalization Note** The filtration `ℱ` is any filtration on `Ω` (the paper's `ℋ` is one); the
shock of period `t + 1` is `ℱ (t + 1)`-measurable and is conditioned on `ℱ t` (the index convention
of `BanditAlgorithm.self_normalized_martingale_bound`). The conditional log-MGF bound is Mathlib's
`HasCondSubgaussianMGF` with variance proxy `σ̄²`, which also asserts integrability of every
`e^{sε_t}` (it needs `StandardBorelSpace Ω`). `σ̄ > 0` is required: the paper divides by `σ̄`. -/
structure Assumption3 {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (σbar : ℝ)
    (ε : ℕ → Ω → ℝ) : Prop where
  sigma_pos : 0 < σbar
  measurable : ∀ t : ℕ, Measurable[ℱ (t + 1)] (ε (t + 1))
  condExp_eq_zero : ∀ t : ℕ, P[ε (t + 1) | ℱ t] =ᵐ[P] 0
  subgaussian : ∀ t : ℕ,
    HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (ε (t + 1)) (σbar ^ 2).toNNReal P

/-- The regressor process `z_t = (x_t, p_t x_t)` of a covariate sequence `x` and a price process
`p` (arXiv:2112.13254v3, p.5). -/
def zProc {Ω : Type} {d : ℕ} (x : ℕ → Fin d → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Fin (d + d) → ℝ :=
  z (x t) (p t ω)

/-- The demand `D_t = g(x_tᵀα* + x_tᵀβ* · p_t) + ε_t`, arXiv:2112.13254v3, (1), p.4. -/
noncomputable def demand {Ω : Type} {d : ℕ} (g : ℝ → ℝ) (θstar : Fin (d + d) → ℝ)
    (x : ℕ → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  g (zProc x p t ω ⬝ᵥ θstar) + ε t ω

/-- The residual `ξ_t(θ) = D_t − g(z_tᵀθ)`, arXiv:2112.13254v3, Appendix C.1.1, p.25. -/
noncomputable def xi {Ω : Type} {d : ℕ} (g : ℝ → ℝ) (θstar : Fin (d + d) → ℝ)
    (x : ℕ → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) (θ : Fin (d + d) → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  demand g θstar x ε p t ω - g (zProc x p t ω ⬝ᵥ θ)

/-- The sampled design matrix `M_t = λ I_{2d} + Σ_{t′=1}^t z_{t′} z_{t′}ᵀ`, arXiv:2112.13254v3,
§3.1, p.6. `M_0 = λ I_{2d}`.

**Formalization Note** This is the published `BanditAlgorithm.regularizedDesignMatrix` in dimension
`d + d` applied to the regressor process. -/
noncomputable def designM {Ω : Type} {d : ℕ} (lam : ℝ) (x : ℕ → Fin d → ℝ) (p : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : Matrix (Fin (d + d)) (Fin (d + d)) ℝ :=
  BanditAlgorithm.regularizedDesignMatrix (d + d) lam (zProc x p) t ω

/-- The regret `Reg_T(x_1, …, x_T) = Σ_{t=1}^T r*(a*_t, b*_t) − E[Σ_{t=1}^T r_t]` with
`a*_t = x_tᵀα*`, `b*_t = x_tᵀβ*` and the realized revenue `r_t = p_t D_t`, arXiv:2112.13254v3,
§2, p.5.

**Formalization Note** The covariates are a deterministic sequence (no expectation is taken over
them, p.5). The expectation is the Bochner integral of the summed realized revenue. -/
noncomputable def regret {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) {d : ℕ}
    (g : ℝ → ℝ) (plo phi : ℝ) (θstar : Fin (d + d) → ℝ) (x : ℕ → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (p : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, rstar g plo phi (x t ⬝ᵥ alphaOf θstar) (x t ⬝ᵥ betaOf θstar) -
    ∫ ω, ∑ t ∈ Finset.Icc 1 T, p t ω * demand g θstar x ε p t ω ∂P

end DynPricingCov


