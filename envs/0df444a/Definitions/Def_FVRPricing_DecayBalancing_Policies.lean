-- Prove2me | Definitions.Def_FVRPricing_DecayBalancing_Policies
-- name    : FVRPricing_DecayBalancing_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:06.814171+00:00
-- url     : https://prove2.me/theorems/4b58134b-a99c-4563-ba21-48956109e67d
-- title:
--   $\tilde J$, the balance price, the decay balancing policy $\pi_{\rm db}$, the optimal price $\pi^*$, the no-learning value $J^{nl}$ and the upper-bounding value $J^{ub}$
-- statement:
--   All objects below are built on the sales model with a $\mathrm{Gamma}(a,b)$ prior, $\mu(z) = a/b$, and discount rate $\alpha$.
--
--   1. **Approximate value** (§4.2, p. 11): $\tilde J(x,a,b) = E[J^*_\lambda(x)]$, $\lambda\sim\mathrm{Gamma}(a,b)$.
--   2. **Balance price**: for a value $V$ and mean $\mu$, the $p\ge0$ solving
--   $$\frac{\bar F(p)}{\rho(p)}\,\mu = \alpha V$$
--   (taken as the infimum of the solution set; Lemma 4 shows it is a singleton for $V=\tilde J$).
--   3. **Decay balancing policy** (eq. (5), p. 13): $\pi_{\rm db}(z)$ is the balance price with $V = \tilde J(z)$, i.e. $\frac{\bar F(\pi_{\rm db}(z))}{\rho(\pi_{\rm db}(z))}\mu(z) = \alpha\tilde J(z)$.
--   4. **Optimal price** (p. 13): $\pi^*(z)$ is the balance price with $V = J^*(z)$, i.e. $\frac{\bar F(\pi^*(z))}{\rho(\pi^*(z))}\mu(z) = \alpha J^*(z)$, the characterization of $\pi^*$ derived from the HJB equation.
--   5. **Known-rate optimal price** (p. 8 and eq. (6), p. 19): $\pi^*_\mu(x)$ solves $\pi^*_\mu(x) = 1/\rho(\pi^*_\mu(x)) + J^*_\mu(x) - J^*_\mu(x-1)$.
--   6. **No-learning value** (p. 19 and the proof of Theorem 1, p. 20): with $\mu=a/b$ and $\pi^{nl}(x') = \pi^*_\mu(x')$, $J^{nl}(x,a,b) = E_\lambda[J^{\pi^{nl}}_\lambda(x)]$.
--   7. **Upper-bounding value** (p. 21): $J^{ub}(z) = E_z[R^{ub}(z)]$, $R^{ub}(z) = \sum_{k:t_k\le\tau} e^{-\alpha t_k}\pi^*(z_{t_k-})$, where the sales process is driven by $\pi_{\rm db}$.
--
--   These are the heuristic of the paper and the comparison objects of its analysis.
--
--   **Formalization Note** $\pi^*$ is the balance price of p. 13, not "some optimal policy": a policy changed at a single $b$-value has the same value, so a statement quantified over all optimal policies would be false at individual states. Values in $[0,\infty]$ are converted to reals only inside the balance equations; Lemma 3 shows they are finite there. The solution sets are taken as `sInf` and are non-empty for $x\ge1$ (Lemma 4); at $x=0$ the prices are never used. $J^{ub}$ uses the general $\alpha$ in place of the $\alpha = e^{-1}$ of p. 21 (the normalization of p. 18).
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 11, §4.2 (J̃); p. 13, §4.3 (balance characterization of π*, eq. (5)); p. 8 and p. 19, eq. (6); p. 20, proof of Theorem 1; p. 21, §6.2 (R^ub, J^ub)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_SalesModel

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

/-- `J̃(x, a, b) = E[J*_λ(x)]` with `λ ~ Gamma(a, b)` (§4.2, p. 11). -/
noncomputable def Jtilde (f : ℝ → ℝ) (α : ℝ) (x : ℕ) (a b : ℝ) : ENNReal :=
  ∫⁻ lam, JstarKnown f α lam x ∂(gammaMeasure a b)

/-- The balance price: the `p ≥ 0` with `F̄(p)/ρ(p) · μ = α V` (taken as the infimum of the solution
set, which Lemma 4 shows is a singleton for `V = J̃`). -/
noncomputable def balancePrice (f : ℝ → ℝ) (α V μ : ℝ) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ Fbar f p / hazard f p * μ = α * V}

/-- Decay balancing policy (5), p. 13: `F̄(π_db(z))/ρ(π_db(z)) μ(z) = α J̃(z)`, `μ(z) = a/b`. -/
noncomputable def πdb (f : ℝ → ℝ) (α : ℝ) : ℕ → ℝ → ℝ → ℝ :=
  fun x a b => balancePrice f α (Jtilde f α x a b).toReal (a / b)

/-- The optimal price characterized by the balance equation of p. 13:
`F̄(π*(z))/ρ(π*(z)) μ(z) = α J*(z)`. -/
noncomputable def πstar (f : ℝ → ℝ) (α : ℝ) : ℕ → ℝ → ℝ → ℝ :=
  fun x a b => balancePrice f α (Jstar f α x a b).toReal (a / b)

/-- Known-rate optimal price at rate `μ`, eq. (6) / p. 8:
`π*_μ(x) = 1/ρ(π*_μ(x)) + J*_μ(x) − J*_μ(x − 1)`. -/
noncomputable def knownOptPrice (f : ℝ → ℝ) (α μ : ℝ) : ℕ → ℝ :=
  fun x => sInf {p : ℝ | 0 ≤ p ∧
    p = 1 / hazard f p + (JstarKnown f α μ x).toReal - (JstarKnown f α μ (x - 1)).toReal}

/-- `J^nl(x, a, b) = E_λ[J^{π^nl}_λ(x)]`, the no-learning scheme `π^nl = π*_μ` with `μ = a/b`
(eq. (6), p. 19; proof of Theorem 1, p. 20). -/
noncomputable def Jnl (f : ℝ → ℝ) (α : ℝ) (x : ℕ) (a b : ℝ) : ENNReal :=
  ∫⁻ lam, JpiKnown f α lam (knownOptPrice f α (a / b)) x ∂(gammaMeasure a b)

/-- `J^ub(z) = E_z[R^ub(z)]` (p. 21): state evolution under `π_db`, payment `π*(z_{t_k−})` at each sale. -/
noncomputable def Jub (f : ℝ → ℝ) (α : ℝ) (x : ℕ) (a b : ℝ) : ENNReal :=
  ∫⁻ lam, ∫⁻ e, pathRevenue f α (πdb f α) (πstar f α) x a b lam e ∂(clockLaw x) ∂(gammaMeasure a b)

end FVRPricing.DecayBalancing


