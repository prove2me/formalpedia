-- Prove2me | Definitions.Def_actuarial_faN
-- name    : actuarial_faN
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:23:53.388402+00:00
-- url     : https://prove2.me/theorems/f1570f97-4873-41fd-a1dd-26cfa66c50fe
-- title:
--   N
-- statement:
--   The finite forward survivor sum N_x accumulates D values up to but not including the terminal age. It is the whole-life annuity-due numerator.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives

namespace ActuarialFoundations

noncomputable def faN (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), faDiscountedLives l v (x+k)

end ActuarialFoundations


