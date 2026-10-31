-- Prove2me | Definitions.Def_RetailTheft_Uniform
-- name    : RetailTheft_Uniform
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:18.310997+00:00
-- url     : https://prove2.me/theorems/ece2597e-5c4c-4ba2-8ac3-b04998464942
-- title:
--   Uniform demand $\varepsilon\sim U[1-\alpha,1+\alpha]$, thresholds $\lambda_1,\lambda_2$, the price $p^*$ of Proposition EC.3 and $g$ of (EC.25)
-- statement:
--   **Uniform instance (§4.2).** For $0<\alpha\le1$, $\varepsilon$ is uniform on $[1-\alpha,1+\alpha]$: its law is Lebesgue measure on that interval scaled by $(2\alpha)^{-1}$. The uniform model has parameters $a,b,c$ and this law.
--
--   **Thresholds (Proposition EC.3).** With $T=\theta/(1+\theta)$ and $X=(b+1)\alpha\theta+(b-1)\theta+b(\alpha+1)$,
--   $$
--   \lambda_1=\frac{2(b-1)}{b(1+\alpha)+\sqrt{b^2(1+\alpha)^2+4(1-b^2)\alpha}}\cdot T,\qquad
--   \lambda_2=\frac{X-\sqrt{X^2-4(b^2-1)\alpha(1+\theta)^2}}{2(b+1)\alpha(1+\theta)}\cdot T.
--   $$
--
--   **Price.** The price $p^*(\lambda)$ of Proposition EC.3 is
--   1. $\dfrac{(1+\theta)\big[b(1+\alpha)+\sqrt{b^2(1+\alpha)^2+4(1-b^2)\alpha}\big]c}{2(b-1)}$ if $\lambda<\lambda_1$;
--   2. $\theta c/\lambda$ if $\lambda_1\le\lambda<\lambda_2$;
--   3. $\dfrac{\big[b(1+\alpha)+\sqrt{\rho(\lambda)}\big]c}{2(b-1)(1-\lambda)}$ if $\lambda_2\le\lambda<T$, where $\rho(\lambda)=b^2(1+\alpha)^2+4(1-b^2)\alpha(1-\lambda)\big[(1+\theta)^2-\theta^2/\lambda\big]$;
--   4. $\dfrac{\big[b(1+\alpha)+\sqrt{b^2(1+\alpha)^2+4(1-b^2)\alpha}\big]c}{2(b-1)(1-\lambda)}$ if $\lambda\ge T$.
--
--   **The function (EC.25).**
--   $$
--   g(\lambda)=\frac{\big(\theta^2/\lambda^2-(1+\theta)^2\big)\,2(1-b^2)\alpha(1-\lambda)}{\sqrt{\rho(\lambda)}}+b(1+\alpha)+\sqrt{\rho(\lambda)}.
--   $$
--
--   These closed forms enter the milestones (Proposition EC.3, Lemma EC.1); the goal theorem is stated about the optimum of the original problem, not about them.
--
--   **Formalization Note** The radicands are nonnegative where used: $b^2(1+\alpha)^2+4(1-b^2)\alpha=b^2(1-\alpha)^2+4\alpha$; $X\ge2(1+\theta)\sqrt{(b^2-1)\alpha}$; and on $0<\lambda\le T$, $(1-\lambda)[(1+\theta)^2-\theta^2/\lambda]\le1$, so $\rho(\lambda)\ge b^2(1-\alpha)^2+4\alpha>0$. The scenarios of $p^*$ are tested in order, which is the printed partition because $\lambda_1\le\lambda_2\le T$. $\lambda<T$ is written $\lambda(1+\theta)<\theta$.
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, §4.2, p. 15 (uniform law); e-companion, Proposition EC.3, pp. ec9–ec10 (λ1, λ2, p*); (EC.25), p. ec12

import Mathlib
import Definitions.Def_RetailTheft_Model

open MeasureTheory

namespace RetailTheft

/-- The uniform law of `ε` on `[1 − α, 1 + α]`, §4.2, p. 15 (PDF 15), of Chen, Tian and Zuo,
*Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft*, MSOM (2025),
doi:10.1287/msom.2025.0024.

**Formalization Note** It is Lebesgue measure restricted to `[1 − α, 1 + α]` and scaled by
`(2α)⁻¹`, a probability measure for `α > 0`. The paper assumes `α ≤ 1`; `α > 0` is the reading
(at `α = 0` the law is a point mass, which this formula does not represent). -/
noncomputable def uniformLaw (α : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * α))⁻¹ • volume.restrict (Set.Icc (1 - α) (1 + α))

/-- The uniform-demand instance of §4.2, p. 15: `D_p = a p^{-b} ε` with `ε ~ U[1 − α, 1 + α]`. -/
noncomputable def uniformModel (a b c α : ℝ) : Params := ⟨a, b, c, uniformLaw α⟩

/-- The threshold `λ₁` of Proposition EC.3, p. ec10 (PDF 43):
`λ₁ = 2(b − 1) / (b(1 + α) + √(b²(1 + α)² + 4(1 − b²)α)) · θ/(1 + θ)`.

**Formalization Note** The radicand equals `b²(1 − α)² + 4α ≥ 0`. -/
noncomputable def lam1 (b α θ : ℝ) : ℝ :=
  2 * (b - 1) / (b * (1 + α) + Real.sqrt (b ^ 2 * (1 + α) ^ 2 + 4 * (1 - b ^ 2) * α)) *
    (θ / (1 + θ))

/-- The threshold `λ₂` of Proposition EC.3, p. ec10 (PDF 43): with
`X = (b + 1)αθ + (b − 1)θ + b(α + 1)`,
`λ₂ = (X − √(X² − 4(b² − 1)α(1 + θ)²)) / (2(b + 1)α(1 + θ)) · θ/(1 + θ)`.

**Formalization Note** For `b > 1`, `α > 0`, `θ ≥ 0` the radicand is nonnegative:
`X ≥ 2(1 + θ)√((b² − 1)α)`, because `b(1 + α) ≥ 2b√α ≥ 2√((b² − 1)α)` and
`(b + 1)α + (b − 1) ≥ 2√((b² − 1)α)`. -/
noncomputable def lam2 (b α θ : ℝ) : ℝ :=
  ((b + 1) * α * θ + (b - 1) * θ + b * (α + 1) -
      Real.sqrt (((b + 1) * α * θ + (b - 1) * θ + b * (α + 1)) ^ 2 -
        4 * (b ^ 2 - 1) * α * (1 + θ) ^ 2)) /
    (2 * (b + 1) * α * (1 + θ)) * (θ / (1 + θ))

/-- The radicand `b²(1 + α)² + 4(1 − b²)α(1 − λ)[(1 + θ)² − θ²/λ]` of scenario 3 of
Proposition EC.3 and of (EC.25).

**Formalization Note** It is only used for `0 < λ ≤ θ/(1 + θ)`, where
`(1 − λ)[(1 + θ)² − θ²/λ] ≤ 1`, so it is at least `b²(1 − α)² + 4α > 0`. -/
noncomputable def rad3 (b α θ lam : ℝ) : ℝ :=
  b ^ 2 * (1 + α) ^ 2 + 4 * (1 - b ^ 2) * α * (1 - lam) * ((1 + θ) ^ 2 - θ ^ 2 / lam)

/-- The optimal price `p*` of Proposition EC.3, pp. ec9–ec10 (PDF 42–43), uniform demand:
1. `λ < λ₁`: `p* = (1 + θ)[b(1 + α) + √(b²(1 + α)² + 4(1 − b²)α)]c / (2(b − 1))`;
2. `λ₁ ≤ λ < λ₂`: `p* = θc/λ`;
3. `λ₂ ≤ λ < θ/(1 + θ)`:
   `p* = [b(1 + α) + √(b²(1 + α)² + 4(1 − b²)α(1 − λ)[(1 + θ)² − θ²/λ])]c / (2(b − 1)(1 − λ))`;
4. `λ ≥ θ/(1 + θ)`: `p* = [b(1 + α) + √(b²(1 + α)² + 4(1 − b²)α)]c / (2(b − 1)(1 − λ))`.

**Formalization Note** The scenarios are tested in order; since `λ₁ ≤ λ₂ ≤ θ/(1 + θ)` (p. ec11)
this is exactly the printed partition. `λ < θ/(1 + θ)` is written `λ(1 + θ) < θ`. Scenarios 2–3
divide by `λ` only where `λ ≥ λ₁`, and they are nonempty only when `θ > 0`, where `λ₁ > 0`. -/
noncomputable def priceStar (b c α θ lam : ℝ) : ℝ :=
  if lam < lam1 b α θ then
    (1 + θ) * (b * (1 + α) + Real.sqrt (b ^ 2 * (1 + α) ^ 2 + 4 * (1 - b ^ 2) * α)) * c /
      (2 * (b - 1))
  else if lam < lam2 b α θ then θ * c / lam
  else if lam * (1 + θ) < θ then
    (b * (1 + α) + Real.sqrt (rad3 b α θ lam)) * c / (2 * (b - 1) * (1 - lam))
  else
    (b * (1 + α) + Real.sqrt (b ^ 2 * (1 + α) ^ 2 + 4 * (1 - b ^ 2) * α)) * c /
      (2 * (b - 1) * (1 - lam))

/-- The function `g` of (EC.25), p. ec12 (PDF 45):
`g(λ) = (θ²/λ² − (1 + θ)²) · 2(1 − b²)α(1 − λ) / √(b²(1 + α)² + 4(1 − b²)α(1 − λ)[(1 + θ)² − θ²/λ])
  + b(1 + α) + √(b²(1 + α)² + 4(1 − b²)α(1 − λ)[(1 + θ)² − θ²/λ])`.

**Formalization Note** The radicand is `rad3`, positive on `(0, θ/(1 + θ)]` (see `rad3`), so the
square root and the division are the paper's there. -/
noncomputable def g (b α θ lam : ℝ) : ℝ :=
  (θ ^ 2 / lam ^ 2 - (1 + θ) ^ 2) * (2 * (1 - b ^ 2) * α * (1 - lam)) /
      Real.sqrt (rad3 b α θ lam) +
    b * (1 + α) + Real.sqrt (rad3 b α θ lam)

end RetailTheft


