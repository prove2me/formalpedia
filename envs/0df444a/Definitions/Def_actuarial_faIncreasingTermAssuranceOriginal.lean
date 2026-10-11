-- Prove2me | Definitions.Def_actuarial_faIncreasingTermAssuranceOriginal
-- name    : actuarial_faIncreasingTermAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:29:17.244821+00:00
-- url     : https://prove2.me/theorems/c77e97d3-905f-4c2f-ba62-e591440096a4
-- title:
--   IncreasingTermAssurance valuation
-- statement:
--   Term increasing death assurance values successively larger benefits for deaths during years one through n, each paid at that year's end.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faIncreasingTermAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := ∑ k ∈ Finset.range n, ((k+1 : ℕ) : ℝ) * v^(k+1) * (faDeaths l (x+k) / l x)

end ActuarialFoundations


