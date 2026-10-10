-- Prove2me | Definitions.Def_actuarial_cm1PremiumAnnuity
-- name    : actuarial_cm1PremiumAnnuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:51:16.000093+00:00
-- url     : https://prove2.me/theorems/d7a05d26-a11d-4430-a543-3b57c98bf012
-- title:
--   Gross premium equivalence: cm1PremiumAnnuity
-- statement:
--   Expected PV of unit level gross premiums payable while the policy is in force. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A_P=\sum_{t<N}v_t p^{\rm inforce}_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1PremiumAnnuity (discount inForce : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, discount t * inForce t

end ActuarialValuation


