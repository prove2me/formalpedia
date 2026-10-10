-- Prove2me | Definitions.Def_actuarial_cm1ReserveYearProfit
-- name    : actuarial_cm1ReserveYearProfit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:53:14.366984+00:00
-- url     : https://prove2.me/theorems/40767204-1b5e-4686-a22b-2d36d2142482
-- title:
--   Projected profits and unit-linked funds: cm1ReserveYearProfit
-- statement:
--   Reserve-adjusted one-year expected profit with opening funds accumulated and an expected survival-weighted closing reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Pi_t=c_t+g_tR_t-s_tR_{t+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1ReserveYearProfit (c s growth R : ℕ → ℝ) (t : ℕ) : ℝ :=
  c t + growth t * R t - s t * R (t+1)

end ActuarialValuation


