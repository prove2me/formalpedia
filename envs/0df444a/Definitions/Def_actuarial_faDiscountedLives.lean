-- Prove2me | Definitions.Def_actuarial_faDiscountedLives
-- name    : actuarial_faDiscountedLives
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:23:24.306596+00:00
-- url     : https://prove2.me/theorems/1bc4d779-d637-4d89-9a78-fcd46dce53a1
-- title:
--   DiscountedLives
-- statement:
--   The D commutation column discounts the original survivors to the table age origin: D_x=v^x l_x. This is not a valuation-age annuity value.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faDiscountedLives (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : ℝ := v^x * l x

end ActuarialFoundations


