-- Prove2me | Definitions.Def_AccelScal_UCRace_ExponentialRace
-- name    : AccelScal_UCRace_ExponentialRace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:40.073644+00:00
-- url     : https://prove2.me/theorems/7d1a6e88-bc94-4297-922a-2eb30413071a
-- title:
--   Independent exponential discovery times
-- statement:
--   Two firms' discovery times have an independent **exponential race law**. If their positive discovery rates are $\lambda_1$ and $\lambda_2$, the joint law of $(\tau_1,\tau_2)$ is the product of the exponential distributions with those rates:
--
--   $$
--   \mathcal E(\lambda_1,\lambda_2)
--     = \operatorname{Exp}(\lambda_1)\otimes\operatorname{Exp}(\lambda_2).
--   $$
--
--   This law fixes the ordering of the two coordinates used in both firms' expected payoffs: the first coordinate is Firm 1's discovery time. The law is reusable for other two-agent first-arrival models.
--
--   **Formalization Note** The definition is total for real rate arguments; all theorem uses impose positive investment intensities and positive technology speed factors, which make both rates positive.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 7, §3.1 and (8)

import Mathlib

noncomputable section

namespace AccelScal.UCRace

/-- The joint law of two independent exponential discovery times. -/
def exponentialRace (rate1 rate2 : ℝ) : MeasureTheory.Measure (ℝ × ℝ) :=
  (ProbabilityTheory.expMeasure rate1).prod (ProbabilityTheory.expMeasure rate2)

end AccelScal.UCRace


