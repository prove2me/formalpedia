-- Prove2me | Definitions.Def_actuarial_faAnnuityArrearsOriginal
-- name    : actuarial_faAnnuityArrearsOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:28:49.641041+00:00
-- url     : https://prove2.me/theorems/c0202d8f-6897-451b-9bd2-787bf4e97407
-- title:
--   AnnuityArrears valuation
-- statement:
--   The annuity in arrears pays at the end of each policy year only on survival to that following anniversary.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faAnnuityArrearsOriginal (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), v^(k+1) * (l (x+k+1) / l x)

end ActuarialFoundations


