-- Prove2me | Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate
-- name    : FalseFailureReturns_TargetRebate_UniformRebate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:36:34.618974+00:00
-- url     : https://prove2.me/theorems/2b4727c0-64e4-4281-a495-c9b9b8e2f879
-- title:
--   Target rebate contract under uniform false failures, Eqs. (6)–(7), and coordination
-- statement:
--   This definition file adds the **target rebate contract** of Ferguson, Guide & Souza (2006), §3–§3.1, under the uniform distribution of false failures.
--
--   Under a target rebate contract $(u, T)$ the retailer receives $u$ dollars for every false failure return below the target level $T$. At effort $\rho$ the number of false failures $X(\rho)$ is uniformly distributed on $[0, 2\beta/\rho]$ (so $E\{X(\rho)\} = \beta/\rho$). The file defines:
--
--   1. the law of $X(\rho)$: Lebesgue measure restricted to $[0, 2\beta/\rho]$ and normalized to total mass one;
--   2. the expected shortfall below the target, $E_X\{[T - X(\rho)]^+\}$, as the genuine expectation of $\max(T - X(\rho), 0)$ under that law;
--   3. the retailer's expected profit under the contract, Eq. (6): $$\pi_R(\rho \mid T, u) = u\,E_X\{[T - X(\rho)]^+\} - \frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big);$$
--   4. the manufacturer's expected profit under the contract, Eq. (7): $$\pi_M(\rho \mid T, u) = M_m\,\beta\Big(1 - \frac{1}{\rho}\Big) - u\,E_X\{[T - X(\rho)]^+\};$$
--   5. **coordination**: the contract $(u, T)$ coordinates the supply chain when the coordinated effort $\rho^C$ of Eq. (2) maximizes the retailer's expected profit $\rho \mapsto \pi_R(\rho \mid T, u)$ over the effort domain $\rho \ge 1$.
--
--   Here $M_m$, $R_r$, $a$, $\beta$ and $\rho^C$ are as in the model definitions. Coordination is the paper's notion ("we find the values of $u$ and $T$ that coordinate this supply chain by equating to (2) the value of $\rho$ that maximizes (6)"): the retailer, choosing its effort to maximize its own profit under the contract, chooses the supply chain's optimal effort.
--
--   **Formalization Note** The expectation is the Bochner integral against `ProbabilityTheory.cond volume (Set.Icc 0 (2 * β / ρ))`; it is not replaced by the closed form $T^2\rho/4\beta$, which holds only when $0 \le T \le 2\beta/\rho$. The integrand is continuous and bounded on the compact support, so the integral is a true expectation whenever $2\beta/\rho > 0$. Coordination is `IsMaxOn` of the retailer's profit on `Set.Ici 1` at `coordEffort P`; it is not the first-order condition.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, pp. 382–383, §3, Eqs. (6)–(7), and §3.1

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model

namespace FalseFailureReturns.TargetRebate

open MeasureTheory

/-- §3.1: the law of the number of false failures `X(ρ) ∼ Uniform(0, 2β/ρ)`, i.e. Lebesgue
measure conditioned on `[0, 2β/ρ]` (a probability measure whenever `2β/ρ > 0`). -/
noncomputable def uniformLaw (β ρ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc 0 (2 * β / ρ))

/-- The expected shortfall below the target, `E_X{[T − X(ρ)]⁺}`, for `X(ρ) ∼ Uniform(0, 2β/ρ)`. -/
noncomputable def expShortfall (β ρ T : ℝ) : ℝ :=
  ∫ x, max (T - x) 0 ∂(uniformLaw β ρ)

/-- Eq. (6) with uniform `X(ρ)`: retailer's expected profit under the target rebate contract
`(u, T)`, `π_R(ρ | T, u) = u E_X{[T − X(ρ)]⁺} − a ρ² / 2 + [r + δ_r(p − w)] β (1 − 1/ρ)`. -/
noncomputable def rebateRetailerProfit (P : Params) (T u ρ : ℝ) : ℝ :=
  u * expShortfall P.β ρ T - P.a * ρ ^ 2 / 2 + P.Rr * P.β * (1 - 1 / ρ)

/-- Eq. (7) with uniform `X(ρ)`: manufacturer's expected profit under the target rebate contract
`(u, T)`, `π_M(ρ | T, u) = (m + δ_m(w − c)) β (1 − 1/ρ) − u E_X{[T − X(ρ)]⁺}`. -/
noncomputable def rebateManufProfit (P : Params) (T u ρ : ℝ) : ℝ :=
  P.Mm * P.β * (1 - 1 / ρ) - u * expShortfall P.β ρ T

/-- pp. 382–383: the contract `(u, T)` coordinates the supply chain when the coordinated effort
`ρ^C` of Eq. (2) maximizes the retailer's expected profit (6) over the effort domain `ρ ≥ 1`. -/
def Coordinates (P : Params) (T u : ℝ) : Prop :=
  IsMaxOn (fun ρ => rebateRetailerProfit P T u ρ) (Set.Ici 1) (coordEffort P)

end FalseFailureReturns.TargetRebate


