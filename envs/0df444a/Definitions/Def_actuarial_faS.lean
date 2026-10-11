-- Prove2me | Definitions.Def_actuarial_faS
-- name    : actuarial_faS
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T23:24:51.659696+00:00
-- url     : https://prove2.me/theorems/0be0d3f1-30c7-4680-99a4-3c41cd6b080b
-- title:
--   S
-- statement:
--   The second-order survivor commutation column S_x is the finite sum of later N values and represents integer-anniversary increasing survivor benefits.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faN

namespace ActuarialFoundations

noncomputable def faS (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : ℝ := ∑ k ∈ Finset.range (ω-x), faN l v ω (x+k)

end ActuarialFoundations


