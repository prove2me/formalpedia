-- Prove2me | Definitions.Def_SeatInventory_Gaussian_Model
-- name    : SeatInventory_Gaussian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:41:54.001934+00:00
-- url     : https://prove2.me/theorems/ebbf1160-d8f3-4337-a15c-aa852479b5f5
-- title:
--   Gaussian EMSR model: tail probability, EMSR, and the protection-level equation (6.10)
-- statement:
--   **The Gaussian two-class EMSR model.** Let $\mu$ be the law of the number of requests $r$ for a fare class, a probability measure on $\mathbb R$. For a real seat level $S$ the **tail probability** is
--   $$\bar P(S) = P[r \ge S] = \mu([S,\infty)),$$
--   and for a fare $f$ the **expected marginal seat revenue** is $\mathrm{EMSR}(S) = \bar P(S)\cdot f$ (Eqs. (6.1)–(6.2)).
--
--   For a mean $\bar r$ and a standard deviation $\hat\sigma$, $N(\bar r, \hat\sigma^2)$ denotes the Gaussian law with that mean and variance $\hat\sigma^2$, and $N(0,1)$ the standard normal law. With class-1 requests $r_1 \sim N(\bar r, \hat\sigma^2)$ and fares $f_1$ (class 1) and $f_2$ (class 2), a real number $S$ is an **EMSR protection level** for class 1 against class 2 when
--   $$\bar P_1(S) = P[r_1 \ge S] = \frac{f_2}{f_1} \qquad \text{(Eq. (6.10))},$$
--   and a real number $Z$ is the **standardized level** for the fare ratio when it "has a probability of $f_2/f_1$ of being exceeded" by a standard normal variable: $P[N(0,1) \ge Z] = f_2/f_1$.
--
--   These are the objects of the sensitivity analysis of Sect. 6.2: the protection level is defined only through the tail equation (6.10), and the standardized level only through the tail equation of $N(0,1)$; the relation $S = \bar r + Z\hat\sigma$ is a theorem of the mission, not part of the definition.
--
--   **Formalization Note** The tail is the real number $\mu([S,\infty))$ (the measure is finite, so no information is lost). $N(\bar r,\hat\sigma^2)$ is Mathlib's `gaussianReal` with variance $\hat\sigma^2$; at $\hat\sigma = 0$ it is the Dirac mass at $\bar r$, and every theorem of the mission assumes $\hat\sigma > 0$. Seat levels are real numbers, as in the book's own Gaussian example ($Z = -0.675$).
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 142, Eq. (6.1)-(6.2); p. 153, Eq. (6.10); pp. 153-154

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.2), p. 142: the probability `P̄(S) = P[r ≥ S]` that the number of
requests `r`, distributed according to the law `μ` on `ℝ`, is at least `S`. -/
noncomputable def tailProb (μ : Measure ℝ) (S : ℝ) : ℝ :=
  (μ (Set.Ici S)).toReal

/-- Belobaba (1987), Eq. (6.1), p. 142: the expected marginal seat revenue
`EMSR(S) = P̄(S) · f` of a fare class with request law `μ` and fare `f`. -/
noncomputable def emsr (μ : Measure ℝ) (f S : ℝ) : ℝ :=
  tailProb μ S * f

/-- The Gaussian request law `N(r̄, σ̂²)` with mean `r̄` and standard deviation `σ̂`
(Mathlib's `gaussianReal` is parameterised by the variance `σ̂² : ℝ≥0`). -/
noncomputable def gaussianLaw (rbar σ : ℝ) : Measure ℝ :=
  gaussianReal rbar ⟨σ ^ 2, sq_nonneg σ⟩

/-- The standard normal law `N(0, 1)`. -/
noncomputable def stdNormal : Measure ℝ :=
  gaussianReal 0 1

/-- Belobaba (1987), Eq. (6.10), p. 153: `S` is an EMSR protection level for class 1 against
class 2 when class-1 requests are `N(r̄, σ̂²)` and the fares are `f₁, f₂`:
`P̄₁(S) = P[r₁ ≥ S] = f₂ / f₁`. -/
def IsProtectionLevel (rbar σ f₁ f₂ S : ℝ) : Prop :=
  tailProb (gaussianLaw rbar σ) S = f₂ / f₁

/-- Belobaba (1987), p. 153–154: `Z` is the standardized normal value "which has a probability
of `f₂/f₁` of being exceeded": `P[N(0,1) ≥ Z] = f₂ / f₁`. -/
def IsStdNormalLevel (f₁ f₂ Z : ℝ) : Prop :=
  tailProb stdNormal Z = f₂ / f₁

end SeatInventory.Gaussian


