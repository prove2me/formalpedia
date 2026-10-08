-- Prove2me | Definitions.Def_CachonCoord_CapacityForecast_Contracts
-- name    : CachonCoord_CapacityForecast_Contracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:55.404744+00:00
-- url     : https://prove2.me/theorems/a9a4b3be-6a53-4e71-bf02-7a17362f2520
-- title:
--   §6.10.2–6.10.3, pp. 99–104 — options and wholesale price contracts, the induced price w_θ(k), and the shares λ_l, λ_h, λ̂_h
-- statement:
--   Contracts in the capacity procurement game of §6.10.
--
--   **Options contract (p. 99).** The manufacturer buys $q_i$ options at $w_o$ each in stage 1 and pays $w_e$ per option exercised in stage 2. When the supplier builds $k = q_i$ (forced compliance), the type-$\theta$ manufacturer's expected profit is
--   $$\Pi_\theta(q_i) = (r - w_e)\,S_\theta(q_i) - w_o q_i,$$
--   and the supplier's is $(w_e - c_p)S_\theta(q_i) + w_o q_i - c_k q_i$. The coordinating options contract with share $\lambda$ has $r - w_e = \lambda(r - c_p)$ and $w_o = \lambda c_k$.
--
--   **Voluntary compliance (p. 100).** A supplier who believes demand is type $\tau$, has sold $q_i$ options and builds $k$ units earns
--   $$\pi(k, q_i, \tau) = (w_e - c_p)S_\tau(k) + w_o q_i - c_k k .$$
--
--   **Wholesale price contract (p. 101).** With wholesale price $w$ the supplier earns $\pi_\theta(k) = (w - c_p)S_\theta(k) - c_k k$; the price that makes capacity $k$ optimal for him is $w_\theta(k) = c_k/\bar F_\theta(k) + c_p$ with $\bar F_\theta = 1 - F_\theta$, and the manufacturer who induces capacity $k$ earns $\Pi_\theta(k) = (r - w_\theta(k))S_\theta(k)$.
--
--   **Separating shares (p. 104).** With optimal capacities $k_h^o, k_l^o$, optimal chain profits $\Omega_\theta^o = \Omega_\theta(k_\theta^o)$ and the supplier's minimum acceptable profit $\hat\pi$:
--   $$\lambda_l = 1 - \frac{\hat\pi}{\Omega_l^o},\qquad \lambda_h = 1 - \frac{\hat\pi}{\Omega_h^o},\qquad \hat\lambda_h = \frac{\Omega_l^o - \hat\pi}{\Omega_l(k_h^o)}.$$
--
--   **Formalization Note** The shares and contract parameters are plain real-valued functions of their arguments; the optimal capacities are passed as arguments and characterized by hypotheses in the theorems that use them. Divisions by $\bar F_\theta(k)$, $\Omega_\theta^o$ and $\Omega_l(k_h^o)$ use Lean's $x/0 = 0$ convention; every theorem using them assumes the denominator positive.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 99 (options contract), p. 100 (π(k, q_i, τ)), p. 101 (wholesale price contract, w_θ(k), Π_θ(k)); §6.10.3, p. 104 (λ_l, λ_h, λ̂_h)

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

namespace Model

variable (M : Model)

/-- Options contract `(w_o, w_e)` (§6.10.2, p. 99): `M` buys `q_i` options at `w_o` each in stage 1
and pays `w_e` per option exercised in stage 2. With `k = q_i` the type-`θ` manufacturer's expected
profit is `Π_θ(q_i) = (r − w_e) S_θ(q_i) − w_o q_i`. -/
noncomputable def mfrProfit (θ : DemandType) (we wo qi : ℝ) : ℝ :=
  (M.r - we) * M.S θ qi - wo * qi

/-- The supplier's expected profit under the options contract `(w_o, w_e)` when he builds
`k = q_i` (forced compliance, §6.10.2–6.10.3, pp. 99–100 and 103): he receives `w_o q_i` and
`w_e S_θ(q_i)`, pays `c_k q_i` for capacity and `c_p S_θ(q_i)` for production. -/
noncomputable def supProfit (θ : DemandType) (we wo qi : ℝ) : ℝ :=
  (we - M.cp) * M.S θ qi + wo * qi - M.ck * qi

/-- The exercise price of the coordinating options contract with share `λ` (`lam`), chosen so that
`r − w_e = λ (r − c_p)` (p. 99). -/
def optWe (lam : ℝ) : ℝ := M.r - lam * (M.r - M.cp)

/-- The option price of the coordinating options contract with share `λ` (`lam`), `w_o = λ c_k`
(p. 99). -/
def optWo (lam : ℝ) : ℝ := lam * M.ck

/-- Voluntary compliance (§6.10.2, p. 100): the profit `π(k, q_i, τ) = (w_e − c_p) S_τ(k) + w_o q_i − c_k k`
of a supplier who believes demand is type `τ` and builds capacity `k` (the page's formula, stated
for `k < q_i`) after selling `q_i` options. -/
noncomputable def supVoluntaryProfit (τ : DemandType) (we wo k qi : ℝ) : ℝ :=
  (we - M.cp) * M.S τ k + wo * qi - M.ck * k

/-- Wholesale price contract under voluntary compliance (§6.10.2, p. 101): the supplier's profit
`π_θ(k) = (w − c_p) S_θ(k) − c_k k` from building capacity `k`. -/
noncomputable def supWholesaleProfit (θ : DemandType) (w k : ℝ) : ℝ :=
  (w - M.cp) * M.S θ k - M.ck * k

/-- The wholesale price that makes capacity `k` optimal for the supplier (p. 101):
`w_θ(k) = c_k / F̄_θ(k) + c_p`, with `F̄_θ(k) = 1 − F(k|θ)`. (If `F̄_θ(k) = 0` Lean's `x / 0 = 0`
gives `c_p`; the theorems using it assume `F̄_θ(k) > 0`.) -/
noncomputable def wInduce (θ : DemandType) (k : ℝ) : ℝ :=
  M.ck / (1 - cdf (M.μ θ) k) + M.cp

/-- The manufacturer's profit when she induces capacity `k` with the wholesale price `w_θ(k)`
(p. 101): `Π_θ(k) = (r − w_θ(k)) S_θ(k)`. -/
noncomputable def mfrWholesaleProfit (θ : DemandType) (k : ℝ) : ℝ :=
  (M.r - M.wInduce θ k) * M.S θ k

/-- The low type's share in the forced-compliance separating contracts (§6.10.3, p. 104),
`λ_l = 1 − π̂ / Ω_l°`, where `kl` is the low type's optimal capacity `k_l°` and `piHat` is the
supplier's minimum acceptable profit `π̂`. -/
noncomputable def shareLow (kl piHat : ℝ) : ℝ := 1 - piHat / M.Omega DemandType.l kl

/-- `λ_h = 1 − π̂ / Ω_h°` (p. 104), `kh` the high type's optimal capacity `k_h°`. -/
noncomputable def shareHigh (kh piHat : ℝ) : ℝ := 1 - piHat / M.Omega DemandType.h kh

/-- `λ̂_h = (Ω_l° − π̂) / Ω_l(k_h°)` (p. 104). -/
noncomputable def shareHighHat (kh kl piHat : ℝ) : ℝ :=
  (M.Omega DemandType.l kl - piHat) / M.Omega DemandType.l kh

end Model

end CachonCoord.CapacityForecast


