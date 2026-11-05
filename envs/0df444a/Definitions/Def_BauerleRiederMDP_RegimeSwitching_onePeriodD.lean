-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodD
-- name    : BauerleRiederMDP_RegimeSwitching_onePeriodD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:10.363058+00:00
-- url     : https://prove2.me/theorems/ad013269-fb48-44b3-80d0-e74773f22c45
-- title:
--   Admissible pairs $D(x)$ of the one-period consumption-investment problem
-- statement:
--   In the one-period consumption-investment problem with interest rate $i$ and relative risk $R\in\mathbb R^d$, an investor with wealth $x\ge0$ consumes $c$ and invests the amounts $a\in\mathbb R^d$ in the risky assets. The **admissible pairs** are
--
--   $$
--   D(x)=\big\{(c,a)\in\mathbb R_+\times\mathbb R^d \;:\; 0\le c\le x,\ (1+i)(x-c+a\cdot R)\ge0\ \ \mathbb P\text{-a.s.}\big\},
--   $$
--
--   the next-period wealth having to lie in $\operatorname{dom}U_p=[0,\infty)$ almost surely.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.3, p.94 (PDF p.108)

import Mathlib
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The admissible consumption-investment pairs of the **one-period consumption-investment
problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.3, p.94, PDF p.108): for wealth `x ∈ dom U_p = [0, ∞)`,
`D(x) = {(c, a) ∈ ℝ_+ × ℝ^d | 0 ≤ c ≤ x and (1 + i)(x − c + a · R) ∈ dom U_p ℙ-a.s.}`,
where `R` is the relative risk with law `μ` and `i` the interest rate.

**Formalization Note.** `dom U_p = [0, ∞)` (standing assumption of §4.3), so membership in
`dom U_p` is `0 ≤ ·`; "ℙ-a.s." is `μ`-a.e. in `z`, `a · z = ∑ k, a k * z k`. -/
def onePeriodD {d : ℕ} (μ : Measure (Fin d → ℝ)) (i x : ℝ) : Set (ℝ × (Fin d → ℝ)) :=
  {ca | 0 ≤ ca.1 ∧ ca.1 ≤ x ∧ ∀ᵐ z ∂μ, 0 ≤ (1 + i) * (x - ca.1 + ∑ k, ca.2 k * z k)}

end BauerleRiederMDP.RegimeSwitching


