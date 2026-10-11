-- Prove2me | Definitions.Def_actuarial_faIncreasingAssuranceOriginal
-- name    : actuarial_faIncreasingAssuranceOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:26:26.490783+00:00
-- url     : https://prove2.me/theorems/009bc85b-68c3-438a-b5dc-62a8038b199f
-- title:
--   IncreasingAssurance valuation
-- statement:
--   Independently valued increasing death benefit pays 1,2,... units on deaths in successive years at each year's end.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

noncomputable def faIncreasingAssuranceOriginal (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * v^(k+1) * (faDeaths l (x+k)/l x)

end ActuarialFoundations


