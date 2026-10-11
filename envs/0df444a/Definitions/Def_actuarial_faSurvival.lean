-- Prove2me | Definitions.Def_actuarial_faSurvival
-- name    : actuarial_faSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:23:14.995499+00:00
-- url     : https://prove2.me/theorems/b2ddb873-c07f-4b94-ae41-e65aaa55cd29
-- title:
--   Survival
-- statement:
--   Conditional n-year survival equals the number alive at age x+n divided by those alive at age x. Its probabilistic interpretation requires strictly positive lives at age x.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faSurvival (l : ℕ → ℝ) (x n : ℕ) : ℝ := l (x+n) / l x

end ActuarialFoundations


