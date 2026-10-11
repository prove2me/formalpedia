-- Prove2me | Definitions.Def_actuarial_faM
-- name    : actuarial_faM
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:24:10.597425+00:00
-- url     : https://prove2.me/theorems/a7b064c7-41fc-4f04-9b9a-ac23da3a15c7
-- title:
--   M
-- statement:
--   The finite forward mortality sum M_x accumulates year-end C values up to the terminal age. It is the whole-life death-assurance numerator.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedDeaths

namespace ActuarialFoundations

noncomputable def faM (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), faDiscountedDeaths l v (x+k)

end ActuarialFoundations


