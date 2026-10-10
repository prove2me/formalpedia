-- Prove2me | Definitions.Def_actuarial_cm1ExpectedBenefitPV
-- name    : actuarial_cm1ExpectedBenefitPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:50:59.089714+00:00
-- url     : https://prove2.me/theorems/5a7263d8-539f-499e-86cf-b2d8593ffcd5
-- title:
--   Gross premium equivalence: cm1ExpectedBenefitPV
-- statement:
--   Expected discounted benefits for each mutually exclusive scenario or calendar payment period. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B=\sum_{t<N}b_t v_t p_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1ExpectedBenefitPV (benefit discount probability : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, benefit t * discount t * probability t

end ActuarialValuation


