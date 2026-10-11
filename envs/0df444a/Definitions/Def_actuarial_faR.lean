-- Prove2me | Definitions.Def_actuarial_faR
-- name    : actuarial_faR
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:25:11.359912+00:00
-- url     : https://prove2.me/theorems/ad384966-81d0-49bd-bb27-457804821134
-- title:
--   R
-- statement:
--   The second-order death commutation column R_x is the finite sum of later M values using relative-duration payment amounts, rather than absolute attained age.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faM

namespace ActuarialFoundations

noncomputable def faR (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), faM l v ω (x+k)

end ActuarialFoundations


