-- Prove2me | Definitions.Def_actuarial_cm1ZeroReserveFloor
-- name    : actuarial_cm1ZeroReserveFloor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:53:40.329984+00:00
-- url     : https://prove2.me/theorems/89266d51-9291-4677-816f-a583bc971914
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveFloor
-- statement:
--   Required opening non-unit reserve is the nonnegative floor that prevents projected reserve-adjusted profit turning negative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_t^*=\max(0,(s_tR_{t+1}-c_t)/g_t)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1ZeroReserveFloor (cash survival growth nextReserve : ℝ) : ℝ :=
  max 0 ((survival * nextReserve - cash) / growth)

end ActuarialValuation


