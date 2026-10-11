-- Prove2me | Definitions.Def_actuarial_faIncreasingTemporaryAnnuityOriginal
-- name    : actuarial_faIncreasingTemporaryAnnuityOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:28:58.161856+00:00
-- url     : https://prove2.me/theorems/6b8cfe0f-0a0a-40a0-973e-0d7be990515b
-- title:
--   IncreasingTemporaryAnnuity valuation
-- statement:
--   Temporary increasing annuity due values independently defined amounts 1,2,...,n at the beginning-year anniversaries.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faIncreasingTemporaryAnnuityOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ) * v^k * (l (x+k) / l x)

end ActuarialFoundations


