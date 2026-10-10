-- Prove2me | Definitions.Def_actuarial_cm1CAREFundingRate
-- name    : actuarial_cm1CAREFundingRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:45:26.334588+00:00
-- url     : https://prove2.me/theorems/aeb87724-b7e5-4453-84e7-26b78430f7c3
-- title:
--   DC contribution accumulation and matching: cm1CAREFundingRate
-- statement:
--   Exact contribution rate required for terminal DC accumulation to match the actuarial capital value of a CARE pension. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c^*=L_{\rm CARE}/F_n
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase

namespace ActuarialValuation

noncomputable def cm1CAREFundingRate (salary revalue terminalGrowth : ℕ → ℝ) (n : ℕ) (accrual annuity : ℝ) : ℝ := cm1CARELiability salary revalue n accrual annuity / cm1AccumulatedSalaryBase salary terminalGrowth n

end ActuarialValuation


