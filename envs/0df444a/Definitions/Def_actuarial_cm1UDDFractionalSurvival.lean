-- Prove2me | Definitions.Def_actuarial_cm1UDDFractionalSurvival
-- name    : actuarial_cm1UDDFractionalSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:50:04.597021+00:00
-- url     : https://prove2.me/theorems/eac483d1-000d-4d91-999e-eb140da52f40
-- title:
--   Select, UDD and constant force: cm1UDDFractionalSurvival
-- statement:
--   Uniform distribution of deaths within a single year gives a linear fractional survival relation; it is not exact without the UDD assumption. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_tp_x=1-tq_x\quad (0\le t\le1)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 6. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def cm1UDDFractionalSurvival (annualSurvival t : ℝ) : ℝ :=
  1 - t * (1 - annualSurvival)

end ActuarialValuation


