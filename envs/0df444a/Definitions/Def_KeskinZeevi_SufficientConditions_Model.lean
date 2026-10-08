-- Prove2me | Definitions.Def_KeskinZeevi_SufficientConditions_Model
-- name    : KeskinZeevi_SufficientConditions_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:13:40.798065+00:00
-- url     : https://prove2.me/theorems/6ca58724-5586-4a3b-8a8f-65d016657476
-- title:
--   Single-product linear demand model: price interval, parameter rectangle, myopic price
-- statement:
--   A seller charges a price $p$ in an interval $[l,u]$ with $0 \le l < u$. Expected demand at price $p$ is linear, $\alpha + \beta p$, with an unknown parameter $\theta = (\alpha,\beta)$ that lies in the compact rectangle
--   $$\Theta = [a_{\min}, a_{\max}] \times [b_{\min}, b_{\max}], \qquad a_{\min} \le a_{\max},\quad b_{\min} \le b_{\max} < 0 .$$
--   The expected single-period revenue is $r_\theta(p) = p(\alpha + \beta p)$, and the revenue-maximizing (myopic) price is
--   $$\varphi(\theta) = -\frac{\alpha}{2\beta},$$
--   with optimal revenue $r^*_\theta = r_\theta(\varphi(\theta))$. The model assumes that $\varphi(\theta)$ lies in the open interval $(l,u)$ for every $\theta \in \Theta$.
--
--   The module also defines the **truncation** of a point $x \in \mathbb{R}^2$ onto $\Theta$, i.e. the Euclidean projection $\arg\min_{\vartheta \in \Theta} \lVert \vartheta - x \rVert$. For a rectangle this projection clamps each coordinate to its interval: $(\max\{a_{\min}, \min\{x_1, a_{\max}\}\}, \max\{b_{\min}, \min\{x_2, b_{\max}\}\})$.
--
--   **Formalization Note.** `Model` bundles the constants $l,u,a_{\min},a_{\max},b_{\min},b_{\max}$ with the standing assumptions of §2 as fields. `phi θ` is the closed form $-\alpha/(2\beta)$. The paper defines $\varphi(\theta)$ as $\arg\max_{p \in [l,u]} r_\theta(p)$, and the interior assumption makes the two agree on $\Theta$. `Model.truncate` is defined directly as coordinatewise clamping. It is not defined as an argmin, because Mathlib's norm on `ℝ × ℝ` is the sup norm, for which the argmin need not be unique.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, pp. 1144-1145, Section 2, Eqs. (2)-(4), and p. 1145 (truncated estimate)

import Mathlib

namespace KeskinZeevi.SufficientConditions

/-- The myopic (revenue-maximizing) price for the single-product linear demand model with
parameter `θ = (α, β)`: `φ(θ) = -α / (2β)` (Keskin–Zeevi 2014, p. 1145). -/
noncomputable def phi (θ : ℝ × ℝ) : ℝ := -θ.1 / (2 * θ.2)

/-- Expected single-period revenue `r_θ(p) = p (α + β p)` (Keskin–Zeevi 2014, (2)). -/
def revenue (θ : ℝ × ℝ) (p : ℝ) : ℝ := p * (θ.1 + θ.2 * p)

/-- Optimal expected single-period revenue `r*_θ = r_θ(φ(θ))`. -/
noncomputable def optRevenue (θ : ℝ × ℝ) : ℝ := revenue θ (phi θ)

/-- The standing assumptions of §2 for a single product (Keskin–Zeevi 2014, pp. 1144–1145):
prices lie in `[l, u]` with `0 ≤ l < u`; the parameter `θ = (α, β)` lies in the compact rectangle
`Θ = [aMin, aMax] × [bMin, bMax]` with `bMax < 0`; and the optimal price `φ(θ)` of every
`θ ∈ Θ` is an interior point of `[l, u]`. -/
structure Model where
  l : ℝ
  u : ℝ
  aMin : ℝ
  aMax : ℝ
  bMin : ℝ
  bMax : ℝ
  zero_le_l : 0 ≤ l
  l_lt_u : l < u
  aMin_le_aMax : aMin ≤ aMax
  bMin_le_bMax : bMin ≤ bMax
  bMax_neg : bMax < 0
  interior : ∀ θ ∈ Set.Icc aMin aMax ×ˢ Set.Icc bMin bMax, phi θ ∈ Set.Ioo l u

/-- The parameter rectangle `Θ = [aMin, aMax] × [bMin, bMax]`. -/
def Model.Theta (M : Model) : Set (ℝ × ℝ) := Set.Icc M.aMin M.aMax ×ˢ Set.Icc M.bMin M.bMax

/-- Projection of a point of `ℝ²` onto the rectangle `Θ` in the Euclidean norm, i.e.
`argmin_{ϑ ∈ Θ} ‖ϑ - x‖`; for a rectangle it is coordinatewise clamping. -/
def Model.truncate (M : Model) (x : ℝ × ℝ) : ℝ × ℝ :=
  (max M.aMin (min x.1 M.aMax), max M.bMin (min x.2 M.bMax))

end KeskinZeevi.SufficientConditions


