-- Prove2me | Definitions.Def_actuarial_faAssuranceOriginal
-- name    : actuarial_faAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:25:46.02636+00:00
-- url     : https://prove2.me/theorems/64f46779-47ef-4b9e-bfda-62802e9cba84
-- title:
--   Assurance valuation
-- statement:
--   The independent death-assurance valuation pays one unit at the end of each year in which death occurs, using original cohort decrements and valuation-age discounting.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), v^(k+1) * (faDeaths l (x+k)/l x)

end ActuarialFoundations


