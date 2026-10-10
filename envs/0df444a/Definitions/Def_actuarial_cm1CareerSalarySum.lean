-- Prove2me | Definitions.Def_actuarial_cm1CareerSalarySum
-- name    : actuarial_cm1CareerSalarySum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:43:40.776566+00:00
-- url     : https://prove2.me/theorems/e2a6c04b-fccd-41c6-a94b-4978f0bea251
-- title:
--   Salary scales and cumulative service: cm1CareerSalarySum
-- statement:
--   Cumulative nominal pensionable earnings for n completed years of service. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_n=\sum_{t<n}S_t
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1CareerSalarySum (salary : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, salary t

end ActuarialValuation


