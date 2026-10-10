-- Prove2me | Definitions.Def_actuarial_cm1LastSurvivorIndicator
-- name    : actuarial_cm1LastSurvivorIndicator
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:51:15.121795+00:00
-- url     : https://prove2.me/theorems/ee6857b7-1890-4c95-8fee-5701fb6e7dc8
-- title:
--   Joint, last-survivor and reversionary benefits: cm1LastSurvivorIndicator
-- statement:
--   Inclusion-exclusion values last survivor status for any joint lifetime distribution. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P(T_x>t\lor T_y>t)=p_x+p_y-p_{xy}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 7. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def cm1LastSurvivorIndicator (pX pY pBoth : ℕ → ℝ) (t : ℕ) : ℝ :=
  pX t + pY t - pBoth t

end ActuarialValuation


