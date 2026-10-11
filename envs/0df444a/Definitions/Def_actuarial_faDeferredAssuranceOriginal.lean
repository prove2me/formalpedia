-- Prove2me | Definitions.Def_actuarial_faDeferredAssuranceOriginal
-- name    : actuarial_faDeferredAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:28:39.433908+00:00
-- url     : https://prove2.me/theorems/626478b3-0ba9-451d-861b-e8eb72f798a9
-- title:
--   DeferredAssurance valuation
-- statement:
--   Deferred death assurance covers deaths from duration m onward and pays at the ends of those years, not on the deferral anniversary.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faDeferredAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (ω x m : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-(x+m)), v^(m+k+1) * (faDeaths l (x+m+k) / l x)

end ActuarialFoundations


