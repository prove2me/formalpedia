-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentSufficient_Model
-- name    : KeskinZeevi_IncumbentSufficient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:14:49.055523+00:00
-- url     : https://prove2.me/theorems/e85d8dfc-82ba-411a-a72f-3a3a47dc4a1b
-- title:
--   Incumbent price model: price interval, incumbent price and demand, slope interval, optimal deviation
-- statement:
--   A seller charges prices $p$ in an interval $[l,u]$ with $0 \le l < u$. Expected demand at price $p$ is linear, $\alpha + \beta p$, but the seller knows one point of the demand curve: at the **incumbent price** $\hat p \in [l,u]$ the expected demand is the known **incumbent demand**
--   $$\hat D = \alpha + \beta \hat p .$$
--   Writing the decision as a deviation $x = p - \hat p$ from the incumbent price, the only unknown is the slope $\beta$, which lies in a known interval $\mathfrak B = [b_{\min}, b_{\max}]$ with $b_{\min} < b_{\max} < 0$. The expected single-period revenue at deviation $x$ is
--   $$r_\beta(x) = (\hat p + x)(\hat D + \beta x),$$
--   and the revenue-maximizing deviation is
--   $$\psi(\beta) = -\frac{\hat p}{2} - \frac{\hat D}{2\beta}.$$
--   The model assumes that the optimal price $\hat p + \psi(\beta)$ lies in the open interval $(l,u)$ for every $\beta \in \mathfrak B$. The optimal revenue is $r_\beta(\psi(\beta))$. The **truncation** of a slope estimate $b$ onto $\mathfrak B$ is $b_{\min} \vee (b \wedge b_{\max}) = \max\{b_{\min}, \min\{b, b_{\max}\}\}$.
--
--   **Formalization Note.** `Model` bundles $l, u, \hat p, \hat D, b_{\min}, b_{\max}$ with the standing assumptions of §2 and §3.4 as fields: $0 \le l < u$, $\hat p \in [l,u]$ (the paper calls $\hat p$ the unique uninformative price "within the feasible price domain $[l,u]$"), $b_{\min} < b_{\max} < 0$, and interiority of $\hat p + \psi(\beta)$ for $\beta \in \mathfrak B$. The paper defines $\psi(\beta)$ in (21) as $\arg\max\{r_\beta(x) : \hat p + x \in [l,u]\}$. The Lean definition is the closed form the paper gives on p. 1150, which is that argmax under the interiority assumption. The intercept $\alpha = \hat D - \beta \hat p$ never appears explicitly.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, pp. 1148-1150, Section 3.4, Eqs. (18), (20), (21), and p. 1150 (closed form of ψ, interiority, truncated estimate)

import Mathlib

namespace KeskinZeevi.IncumbentSufficient

/-- The optimal price deviation of the incumbent price problem in closed form,
`ψ(β) = -p̂/2 - D̂/(2β)` (Keskin–Zeevi 2014, p. 1150, after (21)); `pHat` is the incumbent
price `p̂` and `DHat` the incumbent demand `D̂`. -/
noncomputable def psiOf (pHat DHat β : ℝ) : ℝ := -pHat / 2 - DHat / (2 * β)

/-- The standing assumptions of the incumbent price problem, single product (Keskin–Zeevi 2014,
§2 and §3.4, pp. 1144–1145, 1148–1150): prices lie in `[l, u]` with `0 ≤ l < u`; the incumbent
price `p̂` lies in `[l, u]` and its expected demand `D̂ = α + β p̂` (18) is known; the slope `β`
lies in `𝔅 = [bMin, bMax]` with `bMin < bMax < 0`; and the optimal price `p̂ + ψ(β)` is an
interior point of `[l, u]` for every `β ∈ 𝔅`. -/
structure Model where
  l : ℝ
  u : ℝ
  pHat : ℝ
  DHat : ℝ
  bMin : ℝ
  bMax : ℝ
  zero_le_l : 0 ≤ l
  l_lt_u : l < u
  pHat_mem : pHat ∈ Set.Icc l u
  bMin_lt_bMax : bMin < bMax
  bMax_neg : bMax < 0
  interior : ∀ β ∈ Set.Icc bMin bMax, pHat + psiOf pHat DHat β ∈ Set.Ioo l u

/-- The slope interval `𝔅 = [bMin, bMax]`. -/
def Model.B (M : Model) : Set ℝ := Set.Icc M.bMin M.bMax

/-- The optimal price deviation `ψ(β)` of the model (21). -/
noncomputable def Model.psi (M : Model) (β : ℝ) : ℝ := psiOf M.pHat M.DHat β

/-- Expected single-period revenue as a function of the price deviation `x = p - p̂`,
`r_β(x) = (p̂ + x)(D̂ + β x)` (Keskin–Zeevi 2014, (20)). -/
def Model.revenue (M : Model) (β x : ℝ) : ℝ := (M.pHat + x) * (M.DHat + β * x)

/-- Optimal expected single-period revenue `r_β(ψ(β))`. -/
noncomputable def Model.optRevenue (M : Model) (β : ℝ) : ℝ := M.revenue β (M.psi β)

/-- Projection of a slope estimate onto `𝔅`: `b_min ∨ (b ∧ b_max)` (Keskin–Zeevi 2014, p. 1150). -/
def Model.truncate (M : Model) (b : ℝ) : ℝ := max M.bMin (min b M.bMax)

end KeskinZeevi.IncumbentSufficient


