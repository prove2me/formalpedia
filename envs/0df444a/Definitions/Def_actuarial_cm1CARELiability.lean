-- Prove2me | Definitions.Def_actuarial_cm1CARELiability
-- name    : actuarial_cm1CARELiability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:44:22.733098+00:00
-- url     : https://prove2.me/theorems/d1699567-0e52-4e02-b612-76530cd0a3f1
-- title:
--   Pension accrual and valuation: cm1CARELiability
-- statement:
--   Actuarial capital value of the separately revalued CARE accrual slices. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   L_{\rm CARE}=a_R B_{\rm CARE}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccruedCARE
import Definitions.Def_actuarial_cm1PensionCapitalValue

namespace ActuarialValuation

noncomputable def cm1CARELiability (salary revalue : ℕ → ℝ) (n : ℕ) (accrual annuity : ℝ) : ℝ := cm1PensionCapitalValue (cm1AccruedCARE salary revalue n accrual) annuity

end ActuarialValuation


