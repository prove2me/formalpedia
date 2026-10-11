-- Prove2me | Definitions.Def_actuarial_faDeferredMortality
-- name    : actuarial_faDeferredMortality
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:27:04.479985+00:00
-- url     : https://prove2.me/theorems/1e4fd091-a0b1-4b01-b1b4-5e4073531d25
-- title:
--   DeferredMortality
-- statement:
--   Conditional deferred death probability measures deaths between durations u and u+t from the original valuation-age population.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faDeferredMortality (l : ℕ → ℝ) (x u t : ℕ) : ℝ := (l (x+u) - l (x+u+t)) / l x

end ActuarialFoundations


