-- Prove2me | Definitions.Def_actuarial_cm1ProspectiveCashReserve
-- name    : actuarial_cm1ProspectiveCashReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:52:17.569985+00:00
-- url     : https://prove2.me/theorems/249476a3-0ac1-4591-8cc0-14f11541f7a6
-- title:
--   Prospective reserve and mortality profit: cm1ProspectiveCashReserve
-- statement:
--   Prospective gross reserve is future benefits plus expenses less future gross premium income. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_t=B_t+E_t-P_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1ProspectiveCashReserve (benefits expenses premiums : ℝ) : ℝ :=
  benefits + expenses - premiums

end ActuarialValuation


