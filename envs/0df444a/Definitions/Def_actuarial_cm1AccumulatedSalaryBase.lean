-- Prove2me | Definitions.Def_actuarial_cm1AccumulatedSalaryBase
-- name    : actuarial_cm1AccumulatedSalaryBase
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:44:33.909095+00:00
-- url     : https://prove2.me/theorems/c498c6ea-273f-48c4-a767-3bd1d0994c0b
-- title:
--   DC contribution accumulation and matching: cm1AccumulatedSalaryBase
-- statement:
--   Terminal accumulation base for paying a constant fraction of yearly salary into a DC pension fund. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_n=\sum_{t<n}S_tG_{t\to n}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1AccumulatedSalaryBase (salary terminalGrowth : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, salary t * terminalGrowth t

end ActuarialValuation


