-- Prove2me | Definitions.Def_actuarial_faOneYearMortality
-- name    : actuarial_faOneYearMortality
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:26:44.758006+00:00
-- url     : https://prove2.me/theorems/a00bbd80-549f-4e46-b1d2-92d5a18f8046
-- title:
--   One-year Mortality
-- statement:
--   The conditional one-year mortality ratio uses annual deaths divided by initial survivors; a positive denominator is required to interpret this as q_x.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faOneYearMortality (l : ℕ → ℝ) (x : ℕ) : ℝ := faDeaths l x / l x

end ActuarialFoundations


