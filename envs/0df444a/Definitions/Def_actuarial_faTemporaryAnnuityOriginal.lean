-- Prove2me | Definitions.Def_actuarial_faTemporaryAnnuityOriginal
-- name    : actuarial_faTemporaryAnnuityOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:27:34.831827+00:00
-- url     : https://prove2.me/theorems/3b266715-4f4d-491b-a1e3-805ea650ca4f
-- title:
--   TemporaryAnnuity valuation
-- statement:
--   Temporary annuity due pays at the first n beginning-year anniversaries conditional on survival, independently of any N commutation ratio.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faTemporaryAnnuityOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, v^k * (l (x+k) / l x)

end ActuarialFoundations


