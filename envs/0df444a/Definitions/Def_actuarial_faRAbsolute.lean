-- Prove2me | Definitions.Def_actuarial_faRAbsolute
-- name    : actuarial_faRAbsolute
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:26:05.361162+00:00
-- url     : https://prove2.me/theorems/c5763276-e51a-45ab-a608-e1c0b875fc18
-- title:
--   RAbsolute
-- statement:
--   The absolute-age increasing assurance column weights each discounted death by attained age plus one. Its relationship to relative-duration R_x requires an adjustment of x M_x.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedDeaths

namespace ActuarialFoundations

noncomputable def faRAbsolute (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), ((x+k+1 : ℕ) : ℝ) * faDiscountedDeaths l v (x+k)

end ActuarialFoundations


