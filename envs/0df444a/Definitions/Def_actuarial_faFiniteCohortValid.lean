-- Prove2me | Definitions.Def_actuarial_faFiniteCohortValid
-- name    : actuarial_faFiniteCohortValid
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:22:55.609115+00:00
-- url     : https://prove2.me/theorems/5c27512f-7790-402c-837f-6c4d2b0a62e5
-- title:
--   Finite closed life-table cohort validity
-- statement:
--   A finite closed cohort has nonnegative survivor counts and a zero-life terminal age. The number of survivors cannot increase from one integer age to the next. Conditional probabilities require a separately positive starting count.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., Chapter 3. https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521 Original-derived finite-cohort definition; not a verbatim theorem from the book.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faFiniteCohortValid (l : ℕ → ℝ) (ω : ℕ) : Prop := l ω = 0 ∧ (∀ x, x ≤ ω → 0 ≤ l x) ∧ (∀ x, x < ω → l (x+1) ≤ l x)

end ActuarialFoundations


