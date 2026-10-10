-- Prove2me | Definitions.Def_actuarial_cm1NonUnitCashflow
-- name    : actuarial_cm1NonUnitCashflow
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:53:08.65287+00:00
-- url     : https://prove2.me/theorems/b3b055a3-11a7-4bf0-8dc7-bfce3b924ac7
-- title:
--   Projected profits and unit-linked funds: cm1NonUnitCashflow
-- statement:
--   The net non-unit insurer cashflow separates expense and claim outgo from premium and other charge income. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c_t=P_t+C_t-E_t-B_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1NonUnitCashflow (premium charges expenses claims : ℝ) : ℝ :=
  premium + charges - expenses - claims

end ActuarialValuation


