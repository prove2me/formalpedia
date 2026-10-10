-- Prove2me | Definitions.Def_actuarial_cm1JointLifeAnnuity
-- name    : actuarial_cm1JointLifeAnnuity
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:52:20.077278+00:00
-- url     : https://prove2.me/theorems/d8bbf8af-66e4-4378-87d9-b36163be4009
-- title:
--   Joint, last-survivor and reversionary benefits: cm1JointLifeAnnuity
-- statement:
--   The joint-life annuity pays only when both lives survive each scheduled payment date. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a_{xy}=\sum_{t<n}v_t p_{xy}(t)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 7. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ActuarialValuation

noncomputable def cm1JointLifeAnnuity (discount both : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, discount t * both t

end ActuarialValuation


