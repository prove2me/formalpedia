-- Prove2me | Definitions.Def_KeskinZeevi_LowerBound_Model
-- name    : KeskinZeevi_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:11:34.991408+00:00
-- url     : https://prove2.me/theorems/4eb501f8-0595-4cfb-b5ee-50ac57bc46d2
-- title:
--   Single-product linear-demand pricing model with its standing assumptions
-- statement:
--   A **model** fixes the data of the single-product dynamic pricing problem of Keskin and Zeevi (2014), §2 and §3.1.
--
--   - Feasible prices form the interval $[l,u]$ with $0 \le l < u$.
--   - The unknown demand parameter $\theta = (\alpha,\beta)$ lies in the compact rectangle
--   $$\Theta = [a_{\min}, a_{\max}] \times [b_{\min}, b_{\max}] \subseteq \mathbb{R}^2,$$
--   with $a_{\min} < a_{\max}$ and $b_{\min} < b_{\max} < 0$.
--   - The demand shocks have standard deviation $\sigma > 0$.
--   - For every $\theta = (\alpha,\beta) \in \Theta$ the price $-\alpha/(2\beta)$ lies in the open interval $(l,u)$.
--
--   On top of the model, three functions are defined. The expected single-period revenue (2) is $r_\theta(p) = p(\alpha + \beta p)$. The revenue-maximizing price is $\varphi(\theta) = -\alpha/(2\beta)$. The optimal single-period revenue is $r^*_\theta = r_\theta(\varphi(\theta))$.
--
--   **Formalization Note.** The paper defines $\varphi(\theta)$ as the maximizer (3) of $r_\theta$ over $[l,u]$ and assumes that it is interior. The closed form $-\alpha/(2\beta)$ is what (3) evaluates to under that assumption (p. 1145), so $\varphi$ is defined by the closed form, and interiority is a field of the model. The paper says $\Theta$ is a compact rectangle and that its slopes lie in $[b_{\min}, b_{\max}]$. Here the rectangle is taken to be exactly $[a_{\min},a_{\max}]\times[b_{\min},b_{\max}]$. Nonempty interior ($a_{\min}<a_{\max}$, $b_{\min}<b_{\max}$) is stated explicitly. The proof of Lemma 1 relies on it through a prior density that is positive on the interior of $\Theta$ (p. 1155), and without it Theorem 1 fails: with $\alpha$ or $\beta$ known, the seller learns at a faster rate.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, pp. 1144-1145, Section 2, Eqs. (2)-(3), and p. 1145, Section 3.1

import Mathlib

namespace KeskinZeevi.LowerBound

/-- The single-product linear-demand pricing model of Keskin and Zeevi (2014), §2 and §3.1
(pp. 1144–1145), with its standing assumptions as fields.

* Feasible prices form the interval `[l, u]` with `0 ≤ l < u`.
* Nature draws the parameter `θ = (α, β)` from the compact rectangle
  `Θ = [aMin, aMax] × [bMin, bMax]` (the slope interval is `[b_min, b_max]` with
  `−∞ < b_min < b_max < 0`, p. 1145).
* `Θ` has nonempty interior (`aMin < aMax` and `bMin < bMax`); the proof of Lemma 1 (p. 1155)
  places a prior density on `Θ` that is positive on its interior.
* For every `θ ∈ Θ` the optimal price `−α / (2β)` is an interior point of `[l, u]` (pp. 1144–1145).
* The demand shocks have standard deviation `σ > 0`. -/
structure Model where
  /-- lower end of the feasible price interval -/
  l : ℝ
  /-- upper end of the feasible price interval -/
  u : ℝ
  /-- lower end of the range of the intercept `α` -/
  aMin : ℝ
  /-- upper end of the range of the intercept `α` -/
  aMax : ℝ
  /-- lower end of the range of the slope `β` (the paper's `b_min`) -/
  bMin : ℝ
  /-- upper end of the range of the slope `β` (the paper's `b_max`) -/
  bMax : ℝ
  /-- standard deviation of the demand shocks -/
  σ : ℝ
  l_nonneg : 0 ≤ l
  l_lt_u : l < u
  aMin_lt_aMax : aMin < aMax
  bMin_lt_bMax : bMin < bMax
  bMax_neg : bMax < 0
  σ_pos : 0 < σ
  /-- the revenue-maximizing price `−α / (2β)` lies in the open interval `(l, u)` for every
  `(α, β) ∈ Θ` -/
  interior : ∀ α ∈ Set.Icc aMin aMax, ∀ β ∈ Set.Icc bMin bMax,
    l < -α / (2 * β) ∧ -α / (2 * β) < u

/-- The parameter set `Θ = [aMin, aMax] × [bMin, bMax] ⊆ ℝ²`; a point is `θ = (α, β)`. -/
def Model.Θ (M : Model) : Set (ℝ × ℝ) :=
  Set.Icc M.aMin M.aMax ×ˢ Set.Icc M.bMin M.bMax

/-- Expected single-period revenue (2), single product: `r_θ(p) = p (α + β p)` for
`θ = (α, β)`. -/
def revenue (θ : ℝ × ℝ) (p : ℝ) : ℝ :=
  p * (θ.1 + θ.2 * p)

/-- The revenue-maximizing price `φ(θ) = −α / (2β)` (p. 1145). By `Model.interior` it lies in
`(l, u)` for every `θ ∈ Θ`, where it is the maximizer (3) of `r_θ` over `[l, u]`. -/
noncomputable def optPrice (θ : ℝ × ℝ) : ℝ :=
  -θ.1 / (2 * θ.2)

/-- The optimal expected single-period revenue `r*_θ = r_θ(φ(θ))` (p. 1145). -/
noncomputable def optRevenue (θ : ℝ × ℝ) : ℝ :=
  revenue θ (optPrice θ)

end KeskinZeevi.LowerBound


