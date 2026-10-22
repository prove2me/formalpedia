-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
-- name    : KeskinZeevi_IncumbentLowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:25:08.037241+00:00
-- url     : https://prove2.me/theorems/7fe90b64-8426-43f9-8732-c11a94127468
-- title:
--   Single-product incumbent price model with its standing assumptions
-- statement:
--   A **model** fixes the data of the incumbent price variant of the single-product dynamic pricing problem of Keskin and Zeevi (2014), §3.4.
--
--   - Feasible prices form the interval $[l,u]$ with $0 \le l < u$.
--   - The seller knows an **incumbent price** $\hat p \in [l,u]$ and the **incumbent demand** $\hat D \ne 0$, the expected demand at $\hat p$. By the incumbent price relation (18), $\hat D = \alpha + \beta \hat p$, so the intercept is $\alpha = \hat D - \beta \hat p$ and the only unknown parameter is the slope $\beta$.
--   - The slope lies in the compact interval $\mathfrak B = [b_{\min}, b_{\max}]$ with $b_{\min} < b_{\max} < 0$.
--   - The demand shocks have standard deviation $\sigma > 0$.
--   - For every $\beta \in \mathfrak B$ the price $\hat p/2 - \hat D/(2\beta)$ lies in the open interval $(l,u)$.
--
--   Writing the seller's decision as the deviation $x = p - \hat p$ from the incumbent price, three functions are defined on top of the model. The single-period revenue (20) is
--   $$r_\beta(x) = (\hat p + x)(\hat D + \beta x).$$
--   The optimal deviation (21) is $\psi(\beta) = -\hat p/2 - \hat D/(2\beta)$, so that $\hat p + \psi(\beta) = -\alpha/(2\beta)$ is the revenue-maximizing price for $\alpha = \hat D - \beta\hat p$. The set of slopes over which the worst-case regret (22) is taken is $\{\beta \in \mathfrak B : \psi(\beta) \ne 0\}$, the slopes for which the incumbent price is not optimal.
--
--   **Formalization Note.** The paper defines $\psi(\beta)$ as the maximizer (21) of $r_\beta$ over $\hat p + x \in [l,u]$ and assumes throughout (§2, restated on p. 1150) that the optimal price is interior. Here $\psi$ is the closed form, which equals (21) under the interior assumption, and the interior assumption is a field. Two hypotheses the paper leaves implicit are explicit fields. The first is $\hat p \in [l,u]$: p. 1148 calls $\hat p$ "the unique uninformative price within the feasible price domain $[l,u]$", and the proof of Theorem 3 uses $\hat J_s \le (u-l)^2 s$. The second is $\hat D \ne 0$. If $\hat D = 0$, then $\psi(\beta) = -\hat p/2$ for every $\beta$, the seller knows the optimal price, and Theorem 3 fails. The proof's constant $c_0 = \sigma^2\hat D^2/(4b_{\min}^4)$ (p. 1158) is positive exactly when $\hat D \ne 0$. The paper's reading is $\hat D > 0$; $\hat D \ne 0$ is the weaker hypothesis the proof needs.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, pp. 1148-1149, Section 3.4, Eqs. (18)-(22), and p. 1145, Section 2

import Mathlib

namespace KeskinZeevi.IncumbentLowerBound

/-- The single-product incumbent price model of Keskin and Zeevi (2014), §2 and §3.4,
pp. 1144–1145 and 1148–1149. Prices lie in `[l, u]` with `0 ≤ l < u`. The seller knows the
incumbent price `pHat` (`p̂`) and the incumbent demand `DHat` (`D̂`), related to the unknown
demand parameters by the incumbent price relation (18) `D̂ = α + β p̂`; so the only unknown is the
slope `β`, drawn from the compact interval `𝔅 = [bMin, bMax]` with `−∞ < bMin < bMax < 0`
(p. 1145, p. 1149). The demand shocks are `N(0, σ²)` with `σ > 0` (p. 1149).

Standing assumptions made explicit as fields:
* `pHat_mem`: the incumbent price is feasible, `p̂ ∈ [l, u]` (p. 1148: "the unique uninformative
  price within the feasible price domain [l, u]"; a price the seller "has been charging");
* `DHat_ne_zero`: `D̂ ≠ 0` (implicit; with `D̂ = 0` the optimal price `p̂/2` is known and the
  lower bound of Theorem 3 fails);
* `interior`: for every `β ∈ 𝔅` the optimal price `p̂ + ψ(β) = p̂/2 − D̂/(2β) = φ((α, β))` is an
  interior point of `[l, u]` (§2, p. 1145, restated for this setting on p. 1150). -/
structure Model where
  /-- lower end of the feasible price interval -/
  l : ℝ
  /-- upper end of the feasible price interval -/
  u : ℝ
  /-- the incumbent price `p̂` -/
  pHat : ℝ
  /-- the incumbent demand `D̂` -/
  DHat : ℝ
  /-- lower end of the slope interval `𝔅` -/
  bMin : ℝ
  /-- upper end of the slope interval `𝔅` -/
  bMax : ℝ
  /-- standard deviation of the Gaussian demand shocks -/
  σ : ℝ
  l_nonneg : 0 ≤ l
  l_lt_u : l < u
  pHat_mem : pHat ∈ Set.Icc l u
  DHat_ne_zero : DHat ≠ 0
  bMin_lt_bMax : bMin < bMax
  bMax_neg : bMax < 0
  σ_pos : 0 < σ
  /-- the optimal price `p̂/2 − D̂/(2β)` is interior to `[l, u]` for every `β ∈ 𝔅` -/
  interior : ∀ β ∈ Set.Icc bMin bMax,
    l < pHat / 2 - DHat / (2 * β) ∧ pHat / 2 - DHat / (2 * β) < u

/-- The parameter interval `𝔅 = [bMin, bMax]` of the slope `β` (p. 1149). -/
def Model.B (M : Model) : Set ℝ :=
  Set.Icc M.bMin M.bMax

/-- Single-period expected revenue (20) as a function of the price deviation `x = p − p̂`:
`r_β(x) = (p̂ + x)(D̂ + β x)`. -/
def Model.revenue (M : Model) (β x : ℝ) : ℝ :=
  (M.pHat + x) * (M.DHat + β * x)

/-- The optimal price deviation (21), `ψ(β) = −p̂/2 − D̂/(2β)`, so that
`p̂ + ψ(β) = φ((α, β)) = −α/(2β)` with `α = D̂ − β p̂`. Under `Model.interior` this is the
maximizer of `r_β(x)` over `p̂ + x ∈ [l, u]` for every `β ∈ 𝔅`. -/
noncomputable def Model.optDev (M : Model) (β : ℝ) : ℝ :=
  -M.pHat / 2 - M.DHat / (2 * β)

/-- The set over which the worst-case regret (22) is taken:
`{β : bMin ≤ β ≤ bMax, ψ(β) ≠ 0}`, i.e. the slopes for which the incumbent price is not
the optimal price (p. 1149). -/
def Model.Bexcl (M : Model) : Set ℝ :=
  {β | β ∈ M.B ∧ M.optDev β ≠ 0}

end KeskinZeevi.IncumbentLowerBound


