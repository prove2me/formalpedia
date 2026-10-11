-- Prove2me | Definitions.Def_actuarial_faTermAssuranceOriginal
-- name    : actuarial_faTermAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:27:49.738646+00:00
-- url     : https://prove2.me/theorems/90906ab6-5ea5-451f-93fc-d5af66aa26a1
-- title:
--   TermAssurance valuation
-- statement:
--   Term death assurance pays at the end of the year of death if it occurs among the first n years, with a year-end v^(k+1) factor.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faTermAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, v^(k+1) * (faDeaths l (x+k) / l x)

end ActuarialFoundations


