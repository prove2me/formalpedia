-- Prove2me | Definitions.Def_actuarial_cm1DeathStrainAtRisk
-- name    : actuarial_cm1DeathStrainAtRisk
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:52:34.031634+00:00
-- url     : https://prove2.me/theorems/db48e0de-e726-4d01-9be0-a6dc417cfec7
-- title:
--   Prospective reserve and mortality profit: cm1DeathStrainAtRisk
-- statement:
--   Death strain at risk is the claim payment less the reserve released on the insured's death. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   DSAR=S-V_{t+1}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1DeathStrainAtRisk (deathBenefit endYearReserve : ℝ) : ℝ :=
  deathBenefit - endYearReserve

end ActuarialValuation


