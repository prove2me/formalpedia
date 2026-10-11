-- Prove2me | Definitions.Def_actuarial_faDeferredAnnuityOriginal
-- name    : actuarial_faDeferredAnnuityOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:28:21.669306+00:00
-- url     : https://prove2.me/theorems/69e58c61-2c5f-458e-be30-565a2fef5674
-- title:
--   DeferredAnnuity valuation
-- statement:
--   Deferred whole-life annuity due starts at duration m and continues at each subsequent anniversary while alive through the finite terminal age.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faDeferredAnnuityOriginal (l : ℕ → ℝ) (v : ℝ) (ω x m : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-(x+m)), v^(m+k) * (l (x+m+k) / l x)

end ActuarialFoundations


