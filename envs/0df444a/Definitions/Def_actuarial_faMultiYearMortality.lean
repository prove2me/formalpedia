-- Prove2me | Definitions.Def_actuarial_faMultiYearMortality
-- name    : actuarial_faMultiYearMortality
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:26:54.331+00:00
-- url     : https://prove2.me/theorems/73e154bf-c4ed-4bc2-a668-b101c8b00f15
-- title:
--   Multi-year Mortality
-- statement:
--   The n-year probability of death is initial survivors less end-of-period survivors divided by the initial alive cohort.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faMultiYearMortality (l : ℕ → ℝ) (x n : ℕ) : ℝ := (l x - l (x+n)) / l x

end ActuarialFoundations


