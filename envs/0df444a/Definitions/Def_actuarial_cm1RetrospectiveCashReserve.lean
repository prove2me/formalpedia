-- Prove2me | Definitions.Def_actuarial_cm1RetrospectiveCashReserve
-- name    : actuarial_cm1RetrospectiveCashReserve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:52:24.868602+00:00
-- url     : https://prove2.me/theorems/0bccb340-8b93-4c70-b011-3e84e096c9b3
-- title:
--   Prospective reserve and mortality profit: cm1RetrospectiveCashReserve
-- statement:
--   Retrospective balance is accumulated premiums less accumulated outgo on one consistent valuation basis. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_t=P^{\rm past}_t-O^{\rm past}_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1RetrospectiveCashReserve (pastPremiums pastOutgo : ℝ) : ℝ :=
  pastPremiums - pastOutgo

end ActuarialValuation


