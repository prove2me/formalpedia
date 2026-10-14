-- Prove2me | Definitions.Def_actuarial_c_frac_cfHalf
-- name    : actuarial_c_frac_cfHalf
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:01:37.684987+00:00
-- url     : https://prove2.me/theorems/4e0695ef-9d9a-4a7f-86ec-ca691b5a9f4d
-- title:
--   Half-year conditional survival under finite constant force, the positive square root of annual survival.
-- statement:
--   Half-year conditional survival under finite constant force, the positive square root of annual survival.
--
--   The fractional time is measured from the start of the policy year. Pure algebraic definitions are not themselves proofs. The probability interpretation requires 0≤p≤1, and finite constant force requires p>0.
-- source:
--   Original derived actuarial definition following Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, fractional mortality. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ActuarialAssurances.Fractional

noncomputable def cfHalf (p : ℝ) : ℝ := Real.sqrt p

end ActuarialAssurances.Fractional


