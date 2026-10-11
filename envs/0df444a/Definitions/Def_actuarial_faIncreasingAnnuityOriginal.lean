-- Prove2me | Definitions.Def_actuarial_faIncreasingAnnuityOriginal
-- name    : actuarial_faIncreasingAnnuityOriginal
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:26:14.186989+00:00
-- url     : https://prove2.me/theorems/ab78bca9-c362-4d0f-9281-a890d2678090
-- title:
--   IncreasingAnnuity valuation
-- statement:
--   An independently defined increasing annuity pays 1,2,... units at successive beginning-year anniversaries while alive, without assuming a commutation formula.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ActuarialFoundations

noncomputable def faIncreasingAnnuityOriginal (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * v^k * (l (x+k)/l x)

end ActuarialFoundations


