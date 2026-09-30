-- Prove2me | Definitions.Def_FalseFailureReturns_TargetRebate_Model
-- name    : FalseFailureReturns_TargetRebate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:36:00.228998+00:00
-- url     : https://prove2.me/theorems/695fc255-a275-4cbf-ba60-600f3fcd1717
-- title:
--   False-failure-returns model: unit profits, coordinated and decentralized effort, Eqs. (1)–(5)
-- statement:
--   This definition file sets up the single-period model of Ferguson, Guide & Souza (2006), §3, in which a manufacturer sells through a retailer and the retailer can exert effort to reduce **false failure returns** (products returned as defective that have no functional defect).
--
--   The data are real numbers: the manufacturing cost $c$, the wholesale price $w$, the retail price $p$, the per-unit costs $m$ (manufacturer) and $r$ (retailer) of processing a false failure return, the unit sale impacts $\delta_m$ and $\delta_r$ of avoiding one false failure, the expected number $\beta$ of false failures at the minimum effort level, and the marginal effort cost $a$. From them the model forms the expected profits of avoiding one false failure return,
--   $$M_m = m + \delta_m (w - c) \quad\text{(manufacturer)},\qquad R_r = r + \delta_r (p - w) \quad\text{(retailer)}.$$
--
--   The retailer's effort is $\rho \ge 1$, its cost is $a\rho^2/2$, and the expected number of false failures is $\beta/\rho$. The file defines:
--
--   1. the coordinated supply chain's expected profit, Eq. (1): $$\Pi(\rho) = (M_m + R_r)\,\beta\Big(1 - \frac{1}{\rho}\Big) - \frac{a\rho^2}{2};$$
--   2. the coordinated effort, Eq. (2): $$\rho^C = \Big[\frac{M_m + R_r}{a}\,\beta\Big]^{1/3};$$
--   3. the retailer's expected profit without a contract, Eq. (3): $$\pi_R(\rho) = -\frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big);$$
--   4. the retailer's decentralized effort, Eq. (4): $$\rho^D = \max\Big\{\Big(\frac{R_r\beta}{a}\Big)^{1/3},\,1\Big\};$$
--   5. the manufacturer's expected profit without a contract, Eq. (5), as a function of the effort: $$\pi_M(\rho) = M_m\,\beta\Big(1 - \frac{1}{\rho}\Big),$$ which the paper evaluates at $\rho = \rho^D$.
--
--   These objects are shared by every statement of the mission: $\rho^C$ is the effort a coordinating contract must induce, and $\rho^D$ and $\pi_R(\rho^D)$, $\pi_M(\rho^D)$ are the no-contract benchmark against which the contract is judged.
--
--   **Formalization Note** The parameters are bundled in a structure `Params` with fields `c w p m r deltaM deltaR β a`; `Params.Mm` and `Params.Rr` are $M_m$ and $R_r$. The definitions impose no sign conditions; the paper's standing assumptions ($a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$) are hypotheses of each theorem. Cube roots are `Real.rpow` with exponent `1/3`, applied to bases that are positive under those assumptions.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, pp. 381–382, §3, Eqs. (1)–(5)

import Mathlib

namespace FalseFailureReturns.TargetRebate

/-- The data of the single-period manufacturer–retailer model of Ferguson, Guide & Souza (2006),
§3, pp. 380–382: manufacturing cost `c`, wholesale price `w`, retail price `p`, the per-unit
false-failure costs `m` (manufacturer) and `r` (retailer), the unit sale impacts `deltaM` (δ_m)
and `deltaR` (δ_r) of avoiding one false failure, the expected number `β` of false failures at the
minimum effort level `ρ = 1`, and the marginal effort cost `a` (effort cost `a ρ² / 2`). -/
structure Params where
  c : ℝ
  w : ℝ
  p : ℝ
  m : ℝ
  r : ℝ
  deltaM : ℝ
  deltaR : ℝ
  β : ℝ
  a : ℝ

namespace Params

/-- Manufacturer's expected profit of avoiding one false failure return, `m + δ_m (w − c)` (p. 381). -/
def Mm (P : Params) : ℝ := P.m + P.deltaM * (P.w - P.c)

/-- Retailer's expected profit of avoiding one false failure return, `r + δ_r (p − w)` (p. 381). -/
def Rr (P : Params) : ℝ := P.r + P.deltaR * (P.p - P.w)

end Params

/-- Eq. (1): expected profit of the coordinated supply chain at retailer effort `ρ`,
`Π(ρ) = (m + δ_m(w − c) + r + δ_r(p − w)) β (1 − 1/ρ) − a ρ² / 2`. -/
noncomputable def coordProfit (P : Params) (ρ : ℝ) : ℝ :=
  (P.Mm + P.Rr) * P.β * (1 - 1 / ρ) - P.a * ρ ^ 2 / 2

/-- Eq. (2): coordinated effort `ρ^C = [(m + δ_m(w − c) + r + δ_r(p − w)) / a · β]^{1/3}`. -/
noncomputable def coordEffort (P : Params) : ℝ :=
  ((P.Mm + P.Rr) / P.a * P.β) ^ ((1 : ℝ) / 3)

/-- Eq. (3): retailer's expected profit without a contract,
`π_R(ρ) = −a ρ² / 2 + [r + δ_r(p − w)] β (1 − 1/ρ)`. -/
noncomputable def retailerProfit (P : Params) (ρ : ℝ) : ℝ :=
  -(P.a * ρ ^ 2) / 2 + P.Rr * P.β * (1 - 1 / ρ)

/-- Eq. (4): decentralized effort `ρ^D = max{([r + δ_r(p − w)] β / a)^{1/3}, 1}`. -/
noncomputable def decentrEffort (P : Params) : ℝ :=
  max ((P.Rr * P.β / P.a) ^ ((1 : ℝ) / 3)) 1

/-- Eq. (5): manufacturer's expected profit without a contract at retailer effort `ρ`,
`π_M(ρ) = [m + δ_m(w − c)] β (1 − 1/ρ)`; the paper evaluates it at `ρ = ρ^D`. -/
noncomputable def manufProfit (P : Params) (ρ : ℝ) : ℝ :=
  P.Mm * P.β * (1 - 1 / ρ)

end FalseFailureReturns.TargetRebate


