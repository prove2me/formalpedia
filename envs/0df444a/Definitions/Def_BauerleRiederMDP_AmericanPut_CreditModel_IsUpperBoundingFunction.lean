-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_IsUpperBoundingFunction
-- name    : BauerleRiederMDP_AmericanPut_CreditModel_IsUpperBoundingFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:37.603954+00:00
-- url     : https://prove2.me/theorems/032018da-adfe-440b-9ed4-6527d33f2f22
-- title:
--   Upper bounding function $b$ of the credit granting model
-- statement:
--   A measurable function $b:\mathbb R\to\mathbb R_+$ is an **upper bounding function** for the credit granting model if there are constants $c_r,\alpha_b\ge0$ with
--   1. $c^+(x)\le c_r\,b(x)$ for all $x$ (the reward of extending; cancelling earns $0$);
--   2. $\displaystyle\int b(x')\,Q^X(dx'\mid x)\le\alpha_b\,b(x)$ for all $x$.
--
--   The condition $g^+\le c_g b$ of Definition 2.5.2 is void since $g\equiv0$. Its existence is assumed in §11.2 and ensures Assumption $(B_N)$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Definition 2.5.2, p.40, PDF 55, for the stopping model of §10.1, p.305, PDF 313, with the data of §11.2, p.340, PDF 348

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

/-- `b` is an **upper bounding function** for the Markov Decision Model of the credit granting problem
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.5.2, p.40,
PDF 55, applied to the stopping model of §10.1, p.305, PDF 313, with the data of §11.2, p.340, PDF 348):
a measurable `b : E → ℝ₊` for which there are `c_r, α_b ∈ ℝ₊` with
(i) `r⁺(x, a) ≤ c_r b(x)` on `D`, i.e. `c⁺(x) ≤ c_r b(x)` (extending earns `r(x, 0) = c(x)`, cancelling earns
`r(x, 1) = g(x) = 0`),
(iii) `∫ b(x') Q(dx'|x, a) ≤ α_b b(x)` on `D`, i.e. `∫ b(x') Q^X(dx'|x) ≤ α_b b(x)` (after cancelling the
substochastic kernel is `0`).
Condition (ii) `g⁺ ≤ c_g b` holds trivially since `g ≡ 0`.

**Formalization Note.** The integral of the nonnegative `b` is a lower Lebesgue integral in `ℝ≥0∞`. -/
def CreditModel.IsUpperBoundingFunction (M : CreditModel) (b : ℝ → ℝ) : Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧
    ∃ cr αb : ℝ, 0 ≤ cr ∧ 0 ≤ αb ∧ (∀ x, max (M.c x) 0 ≤ cr * b x) ∧
      ∀ x, ∫⁻ y, ENNReal.ofReal (b y) ∂(M.QX x) ≤ ENNReal.ofReal (αb * b x)

end BauerleRiederMDP.AmericanPut


