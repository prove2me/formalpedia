-- Prove2me | Definitions.Def_DRSOWass_Duality_Setting
-- name    : DRSOWass_Duality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T11:27:28.636141+00:00
-- url     : https://prove2.me/theorems/e8d65fbb-a431-4411-8f2d-a5da8f5bd7c7
-- title:
--   Wasserstein ball, regularization operator Φ, D̄ and D̲, growth rate κ, dual objective h, v_P and v_D
-- statement:
--   Let $(\Xi,d)$ be a metric space with its Borel $\sigma$-algebra, let $\Psi:\Xi\to\mathbb R$, let $\nu$ be a probability measure on $\Xi$, and let $p\ge 1$, $\theta>0$. This file collects the objects of Sections 2–3 of Gao and Kleywegt.
--
--   1. **Wasserstein distance.** For measures $\mu,\nu$ on $\Xi$,
--   $$W_p^p(\mu,\nu)=\inf\Big\{\int_{\Xi\times\Xi} d^p(\xi,\zeta)\,\gamma(d\xi,d\zeta):\ \gamma\in\mathcal P(\Xi\times\Xi),\ \pi^1_\#\gamma=\mu,\ \pi^2_\#\gamma=\nu\Big\},$$
--   a value in $[0,\infty]$ (Definition 2, (1)).
--   2. **Regularization operator** (Definition 3). $\Phi(\lambda,\zeta)=\inf_{\xi\in\Xi}\{\lambda d^p(\xi,\zeta)-\Psi(\xi)\}\in\mathbb R\cup\{-\infty\}$. For $\varepsilon\ge 0$ the $\varepsilon$-optimal set is $S_\varepsilon(\lambda,\zeta)=\{\xi:\lambda d^p(\xi,\zeta)-\Psi(\xi)\le\Phi(\lambda,\zeta)+\varepsilon\}$, and the arg min is $\{\xi:\lambda d^p(\xi,\zeta)-\Psi(\xi)=\Phi(\lambda,\zeta)\}$.
--   3. **Near-optimal distances** ((3), (4)).
--   $$\overline D(\lambda,\zeta)=\limsup_{\varepsilon\downarrow 0}\sup_{\xi\in S_\varepsilon(\lambda,\zeta)}d^p(\xi,\zeta),\qquad \underline D(\lambda,\zeta)=\liminf_{\varepsilon\downarrow 0}\inf_{\xi\in S_\varepsilon(\lambda,\zeta)}d^p(\xi,\zeta),$$
--   and $\overline D_0$, $\underline D_0$ are the supremum and infimum of $d^p(\xi,\zeta)$ over the arg min.
--   4. **Selection sets** (Lemma 3(ii)). $\overline F^\varepsilon_\delta(\lambda,\zeta)=\{\xi\in S_\varepsilon(\lambda,\zeta): d^p(\xi,\zeta)\ge\overline D(\lambda,\zeta)-\delta\}$ and $\underline F^\varepsilon_\delta(\lambda,\zeta)=\{\xi\in S_\varepsilon(\lambda,\zeta): d^p(\xi,\zeta)\le\underline D(\lambda,\zeta)+\delta\}$.
--   5. **Growth rate** (Definition 4). $\kappa=\inf\{\lambda\ge 0:\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)>-\infty\}\in[0,\infty]$, with $\kappa=\infty$ when no such $\lambda$ exists.
--   6. **Dual objective** (p. 11). $h(\lambda)=\lambda\theta^p-\int_\Xi\Phi(\lambda,\zeta)\,\nu(d\zeta)$.
--   7. **Primal and dual values** (p. 8).
--   $$v_P=\sup_{\mu\in\mathcal P(\Xi)}\Big\{\int_\Xi\Psi\,d\mu:\ W_p(\mu,\nu)\le\theta\Big\},\qquad v_D=\inf_{\lambda\ge 0}h(\lambda).$$
--
--   These are the objects in which the strong duality theorem $v_P=v_D$ and its lemmas are stated.
--
--   **Formalization Note** $W_p^p$ is the published `RWPI.SqrtLasso.transportCost` with cost $d^p$ (an infimum over probability couplings; the paper's "min" is attained, which does not affect the constraint $W_p\le\theta$, written $W_p^p(\mu,\nu)\le\theta^p$). Every integral that may be infinite is the published `ModelRiskOT.Duality.extIntegral`, $\int\varphi^+-\int\varphi^-$ in the extended reals (with $\infty-\infty=-\infty$, which never raises a supremum); in particular $\int\Psi\,d\mu$ in $v_P$ is not the Bochner integral. $\Phi$, $h$, $v_P$, $v_D$ are `EReal`-valued; $\overline D,\underline D,\overline D_0,\underline D_0,\kappa$ are `ENNReal`-valued. The $\varepsilon$-sets grow with $\varepsilon$, so the $\limsup$ in $\overline D$ is the infimum over $\varepsilon>0$ and the $\liminf$ in $\underline D$ is the supremum over $\varepsilon>0$. Outside their domains ($\Phi(\lambda,\zeta)=-\infty$, resp. an empty arg min) the total Lean functions take the default values $\overline D=\overline D_0=0$, $\underline D=\underline D_0=\infty$; no statement of the mission uses these values. $h$ and $\Phi$ are defined for every real $\lambda$; the statements restrict to $\lambda\ge 0$ where the paper does.
-- source:
--   Gao, Kleywegt, Distributionally Robust Stochastic Optimization with Wasserstein Distance, arXiv:1604.02199v3, p. 7, Definition 2 (1); p. 8, (Primal), (Dual); p. 9, Definition 3 (3), (4), Definition 4; p. 10, Lemma 3(ii) (the sets F̄, F̲); p. 11, the dual objective h

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral

open MeasureTheory

namespace DRSOWass.Duality

variable {Ξ : Type*} [MetricSpace Ξ] [MeasurableSpace Ξ]

/-- The `p`-th power of the order-`p` Wasserstein distance, `W_p^p(μ, ν)` of Definition 2, (1):
the infimum, over probability measures `γ` on `Ξ × Ξ` with first marginal `μ` and second
marginal `ν`, of `∫ d^p(ξ, ζ) γ(dξ, dζ)` (a lower Lebesgue integral in `[0, ∞]`; `⊤` when no
such coupling exists). -/
noncomputable def wassPow (p : ℝ) (μ ν : Measure Ξ) : ENNReal :=
  RWPI.SqrtLasso.transportCost (fun ξ ζ => ENNReal.ofReal (dist ξ ζ ^ p)) μ ν

/-- The regularization operator of Definition 3:
`Φ(λ, ζ) = inf_{ξ ∈ Ξ} { λ d^p(ξ, ζ) − Ψ(ξ) }`, a value in `ℝ ∪ {−∞}` (never `+∞`). -/
noncomputable def Phi (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : EReal :=
  ⨅ ξ : Ξ, ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal)

/-- The `ε`-optimal set `{ξ ∈ Ξ : λ d^p(ξ, ζ) − Ψ(ξ) ≤ Φ(λ, ζ) + ε}` of (3). -/
def nearOpt (Ψ : Ξ → ℝ) (p lam ε : ℝ) (ζ : Ξ) : Set Ξ :=
  {ξ | ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal) ≤ Phi Ψ p lam ζ + (ε : EReal)}

/-- The minimizer set `arg min_{ξ ∈ Ξ} { λ d^p(ξ, ζ) − Ψ(ξ) }` of (4). -/
def argminSet (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : Set Ξ :=
  {ξ | ((lam * dist ξ ζ ^ p - Ψ ξ : ℝ) : EReal) = Phi Ψ p lam ζ}

/-- `D̄(λ, ζ)` of (3): `limsup_{ε ↓ 0} sup { d^p(ξ, ζ) : ξ ∈ nearOpt λ ε ζ }`. The sets grow
with `ε`, so the limsup is the infimum over `ε > 0`. Meaningful where `Φ(λ, ζ) > −∞`
(elsewhere every set is empty and the value is `0`). -/
noncomputable def DUpper (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : ENNReal :=
  ⨅ (ε : ℝ) (_ : 0 < ε), ⨆ ξ ∈ nearOpt Ψ p lam ε ζ, ENNReal.ofReal (dist ξ ζ ^ p)

/-- `D̲(λ, ζ)` of (3): `liminf_{ε ↓ 0} inf { d^p(ξ, ζ) : ξ ∈ nearOpt λ ε ζ }`. The sets grow
with `ε`, so the infima shrink and the liminf is the supremum over `ε > 0`. Meaningful where
`Φ(λ, ζ) > −∞` (elsewhere every set is empty and the value is `⊤`). -/
noncomputable def DLower (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : ENNReal :=
  ⨆ (ε : ℝ) (_ : 0 < ε), ⨅ ξ ∈ nearOpt Ψ p lam ε ζ, ENNReal.ofReal (dist ξ ζ ^ p)

/-- `D̄₀(λ, ζ) = sup { d^p(ξ, ζ) : λ d^p(ξ, ζ) − Ψ(ξ) = Φ(λ, ζ) }` of (4). Meaningful where the
arg min is nonempty. -/
noncomputable def DUpper0 (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : ENNReal :=
  ⨆ ξ ∈ argminSet Ψ p lam ζ, ENNReal.ofReal (dist ξ ζ ^ p)

/-- `D̲₀(λ, ζ) = inf { d^p(ξ, ζ) : λ d^p(ξ, ζ) − Ψ(ξ) = Φ(λ, ζ) }` of (4). Meaningful where the
arg min is nonempty. -/
noncomputable def DLower0 (Ψ : Ξ → ℝ) (p lam : ℝ) (ζ : Ξ) : ENNReal :=
  ⨅ ξ ∈ argminSet Ψ p lam ζ, ENNReal.ofReal (dist ξ ζ ^ p)

/-- The set `F̄^ε_δ(λ, ζ) = {ξ : λ d^p(ξ, ζ) − Ψ(ξ) ≤ Φ(λ, ζ) + ε, d^p(ξ, ζ) ≥ D̄(λ, ζ) − δ}` of
Lemma 3(ii). -/
def FUpper (Ψ : Ξ → ℝ) (p lam δ ε : ℝ) (ζ : Ξ) : Set Ξ :=
  {ξ | ξ ∈ nearOpt Ψ p lam ε ζ ∧
    DUpper Ψ p lam ζ - ENNReal.ofReal δ ≤ ENNReal.ofReal (dist ξ ζ ^ p)}

/-- The set `F̲^ε_δ(λ, ζ) = {ξ : λ d^p(ξ, ζ) − Ψ(ξ) ≤ Φ(λ, ζ) + ε, d^p(ξ, ζ) ≤ D̲(λ, ζ) + δ}` of
Lemma 3(ii). -/
def FLower (Ψ : Ξ → ℝ) (p lam δ ε : ℝ) (ζ : Ξ) : Set Ξ :=
  {ξ | ξ ∈ nearOpt Ψ p lam ε ζ ∧
    ENNReal.ofReal (dist ξ ζ ^ p) ≤ DLower Ψ p lam ζ + ENNReal.ofReal δ}

/-- The growth rate of Definition 4: `κ = inf { λ ≥ 0 : ∫ Φ(λ, ζ) ν(dζ) > −∞ }`, in `[0, ∞]`,
with `κ = ∞` when the set is empty. -/
noncomputable def growthRate (Ψ : Ξ → ℝ) (ν : Measure Ξ) (p : ℝ) : ENNReal :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam) (_ : ⊥ < ModelRiskOT.Duality.extIntegral ν (Phi Ψ p lam)),
    ENNReal.ofReal lam

/-- The dual objective function of p. 11: `h(λ) = λ θ^p − ∫ Φ(λ, ζ) ν(dζ)`. -/
noncomputable def dualObj (Ψ : Ξ → ℝ) (ν : Measure Ξ) (p θ lam : ℝ) : EReal :=
  ((lam * θ ^ p : ℝ) : EReal) - ModelRiskOT.Duality.extIntegral ν (Phi Ψ p lam)

/-- The primal value of (Primal):
`v_P = sup { ∫ Ψ dμ : μ ∈ P(Ξ), W_p(μ, ν) ≤ θ }`, with `W_p(μ, ν) ≤ θ` written `W_p^p(μ, ν) ≤ θ^p`. -/
noncomputable def vP (Ψ : Ξ → ℝ) (ν : Measure Ξ) (p θ : ℝ) : EReal :=
  ⨆ (μ : Measure Ξ) (_ : IsProbabilityMeasure μ ∧ wassPow p μ ν ≤ ENNReal.ofReal (θ ^ p)),
    ModelRiskOT.Duality.extIntegral μ (fun ξ => (Ψ ξ : EReal))

/-- The dual value of (Dual): `v_D = inf_{λ ≥ 0} h(λ)`. -/
noncomputable def vD (Ψ : Ξ → ℝ) (ν : Measure Ξ) (p θ : ℝ) : EReal :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam), dualObj Ψ ν p θ lam

end DRSOWass.Duality


