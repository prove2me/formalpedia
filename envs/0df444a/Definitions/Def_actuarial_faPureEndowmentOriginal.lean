-- Prove2me | Definitions.Def_actuarial_faPureEndowmentOriginal
-- name    : actuarial_faPureEndowmentOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:27:24.288004+00:00
-- url     : https://prove2.me/theorems/3d516918-8c2a-41cb-a85d-282f7247e376
-- title:
--   PureEndowment valuation
-- statement:
--   An n-year pure endowment pays at time n only if the original life survives to that anniversary, using v^n and n-year survival.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faSurvival

namespace ActuarialFoundations

noncomputable def faPureEndowmentOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := v^n * faSurvival l x n

end ActuarialFoundations


