-- Prove2me | Definitions.Def_actuarial_faDeaths
-- name    : actuarial_faDeaths
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:23:05.155977+00:00
-- url     : https://prove2.me/theorems/aeaebc63-548d-4e7e-aae7-a1b11a54a3ab
-- title:
--   Deaths
-- statement:
--   Annual deaths are the loss of members of the same cohort between ages x and x+1, including the terminal year; the result has units of lives.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faDeaths (l : ℕ → ℝ) (x : ℕ) : ℝ := l x - l (x+1)

end ActuarialFoundations


