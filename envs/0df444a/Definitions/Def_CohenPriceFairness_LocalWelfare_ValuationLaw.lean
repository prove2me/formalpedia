-- Prove2me | Definitions.Def_CohenPriceFairness_LocalWelfare_ValuationLaw
-- name    : CohenPriceFairness_LocalWelfare_ValuationLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:49.379109+00:00
-- url     : https://prove2.me/theorems/78640e53-34af-4053-80dd-e0e697874d71
-- title:
--   Nonnegative valuation law with finite first moment
-- statement:
--   A valuation law is a Borel probability measure $\mu$ on $\mathbb R$, supported almost surely on nonnegative values, with finite first moment: $\int |v|\,d\mu(v)<\infty$. This is a reusable distribution concept, separate from any pricing model. The finite-moment condition gives the source's real-valued expectations their ordinary meaning.
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; §2, pp. 6–7 (valuation distributions and expectations).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare


