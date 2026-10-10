-- Prove2me | Definitions.Def_actuarial_cm1GrossLevelPremium
-- name    : actuarial_cm1GrossLevelPremium
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:51:28.287579+00:00
-- url     : https://prove2.me/theorems/e402aeb9-eac1-4d0c-80e1-dba28f18d52c
-- title:
--   Gross premium equivalence: cm1GrossLevelPremium
-- statement:
--   Under the simple zero-initial-surplus equivalence principle, level gross premium covers expected benefit and expense value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G=(B+E)/A_P
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1GrossLevelPremium (B E A : ℝ) : ℝ := (B+E)/A

end ActuarialValuation


