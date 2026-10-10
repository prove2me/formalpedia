-- Prove2me | Definitions.Def_actuarial_cm1AnnualAccrual
-- name    : actuarial_cm1AnnualAccrual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:44:04.284411+00:00
-- url     : https://prove2.me/theorems/75117ca6-7b20-433f-8789-218bcbe5d132
-- title:
--   Pension accrual and valuation: cm1AnnualAccrual
-- statement:
--   Annual cash pension earned in service year t before subsequent revaluation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   b_t=\alpha S_t
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1AnnualAccrual (salary : ℕ → ℝ) (accrual : ℝ) (t : ℕ) : ℝ := accrual * salary t

end ActuarialValuation


