-- Prove2me | Definitions.Def_actuarial_faDiscountedDeaths
-- name    : actuarial_faDiscountedDeaths
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:23:40.217208+00:00
-- url     : https://prove2.me/theorems/b2a53fc4-63df-45ac-8d19-77dd3eb58c8c
-- title:
--   DiscountedDeaths
-- statement:
--   The C commutation column discounts deaths to the following anniversary: C_x=v^(x+1) d_x. Death benefits are payable at year-end, not year-start.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faDiscountedDeaths (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : ℝ := v^(x+1) * faDeaths l x

end ActuarialFoundations


