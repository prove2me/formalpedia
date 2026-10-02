-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_BoundingFunction
-- name    : MDPFinance_BayesianModels_BoundingFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:19:59.165269+00:00
-- url     : https://prove2.me/theorems/ed33ba3b-bf6d-41e3-b156-c5a01b687faa
-- title:
--   Upper bounding function and $IB_b^+$ (stationary)
-- statement:
--   This definition restates Chapter 2's **upper bounding function** machinery, specialized to
--   a stationary model with raw data $(D,Q,r,g)$: a measurable $b : E \to \mathbb R_{\ge 0}$ is an
--   upper bounding function with constants $(c_r,c_g,\alpha_b)$ if
--   $$
--   r^+(x,a) \le c_r\, b(x), \qquad g^+(x) \le c_g\, b(x), \qquad
--   \int_E b(x')\, Q(\mathrm dx'\mid x,a) \le \alpha_b\, b(x)
--   $$
--   for every feasible $(x,a) \in D$. The associated function space
--   $$
--   IB_b^+ := \Big\{v \in IM(E) \;\Big|\; v^+(x) \le c\, b(x) \text{ for all } x,
--   \text{ for some } c \ge 0\Big\}
--   $$
--   is the standing regularity class the goal Theorem 5.4.10 states its Structure Assumption inside
--   of.
--
--   **Formalization Note.** Restated from `MDPFinance.Semicontinuous.IsUpperBoundingFunction`
--   (chunk `02b`) / `MDPFinance.StructuredModels.IBbPlus` (chunk `02c`), specialized to a stationary
--   model as `MDPFinance.BayesianModels.Top`/`StructureAssumptionOf` are.
--
--   **Moderation note.** The bound $\int b\,dQ\le\alpha_b b$ is a Lebesgue integral ($b\ge 0$), so that a $b$ without finite expectation cannot pass it with a default value; $r^+$, $g^+$ are the positive parts of the $[-\infty,\infty]$-valued rewards.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 28-29, Definition 2.4.1 (stationary form)

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- An upper bounding function (Bäuerle–Rieder, Definition 2.4.1, p. 28, PDF 43, stationary):
a measurable `b : E → ℝ_{≥0}` with `r^+(x,a) ≤ c_r b(x)`, `g^+(x) ≤ c_g b(x)`, and
`∫ b(x') Q(dx'|x,a) ≤ α_b b(x)` (a Lebesgue integral, `b ≥ 0`, so that a `b` without finite
expectation cannot pass the bound with a default value). Restated from
`MDPFinance.Semicontinuous.IsUpperBoundingFunction` (chunk `02b`). -/
structure IsUpperBoundingFunction (D : Set (E × A)) (Q : E × A → Measure E) (r : E × A → EReal)
    (g : E → EReal) (b : E → ℝ) (cr cg αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcg : 0 ≤ cg
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ D, r xa ⊔ 0 ≤ ((cr * b xa.1 : ℝ) : EReal)
  hg : ∀ x, g x ⊔ 0 ≤ ((cg * b x : ℝ) : EReal)
  hQ : ∀ xa ∈ D, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44). Restated from `MDPFinance.StructuredModels.IBbPlus` (chunk `02c`). -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.BayesianModels


