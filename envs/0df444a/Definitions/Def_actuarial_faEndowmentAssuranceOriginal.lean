-- Prove2me | Definitions.Def_actuarial_faEndowmentAssuranceOriginal
-- name    : actuarial_faEndowmentAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:28:13.913542+00:00
-- url     : https://prove2.me/theorems/e92072d1-aef6-48f4-a275-4d57d84086bb
-- title:
--   EndowmentAssurance valuation
-- statement:
--   The n-year endowment assurance combines a term death assurance and a separately timed pure endowment; the two outcomes do not overlap.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faPureEndowmentOriginal
import Definitions.Def_actuarial_faTermAssuranceOriginal

namespace ActuarialFoundations

noncomputable def faEndowmentAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := faTermAssuranceOriginal l v x n + faPureEndowmentOriginal l v x n

end ActuarialFoundations


