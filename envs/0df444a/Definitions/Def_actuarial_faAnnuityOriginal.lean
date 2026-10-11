-- Prove2me | Definitions.Def_actuarial_faAnnuityOriginal
-- name    : actuarial_faAnnuityOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:25:34.102612+00:00
-- url     : https://prove2.me/theorems/f3978d1c-b862-4bae-8d6a-395f20c72fd8
-- title:
--   Annuity valuation
-- statement:
--   The independently valued annuity-due pays one unit at each anniversary on which the member is alive, with each cashflow discounted from the attained valuation age.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faAnnuityOriginal (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), v^k * (l (x+k)/l x)

end ActuarialFoundations


