-- Prove2me | Definitions.Def_actuarial_cm1AccruedCARE
-- name    : actuarial_cm1AccruedCARE
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:43:56.053505+00:00
-- url     : https://prove2.me/theorems/35c82528-83bc-4f79-bf5b-54a6b4333b67
-- title:
--   Salary scales and cumulative service: cm1AccruedCARE
-- statement:
--   Career-average revalued earnings pension accumulates individual annual accrual slices. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_{\rm CARE}=\alpha\sum_{t<n}S_tR_t
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2009), Pension Mathematics, Chapter 9, printed page 291, salary scale and benefit accrual. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 9, salary scale and pension mathematics, https://doi.org/10.1017/CBO9780511800146; pension accrual formula and CARE benefits, https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf; IFoA CM1 2026 syllabus, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf. Parent topic: CM1 pension funding, salary scale projected unit credit, final salary, CARE and terminal value of defined contributions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def cm1AccruedCARE (salary revalue : ℕ → ℝ) (n : ℕ) (accrual : ℝ) : ℝ := accrual * ∑ t ∈ Finset.range n, salary t * revalue t

end ActuarialValuation


