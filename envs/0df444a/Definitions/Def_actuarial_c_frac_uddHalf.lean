-- Prove2me | Definitions.Def_actuarial_c_frac_uddHalf
-- name    : actuarial_c_frac_uddHalf
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:01:25.635987+00:00
-- url     : https://prove2.me/theorems/a94eef46-8236-4544-a8bd-c4e3ea1c4832
-- title:
--   Half-year conditional survival under uniform distribution of deaths.
-- statement:
--   Half-year conditional survival under uniform distribution of deaths.
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

noncomputable def uddHalf (p : ℝ) : ℝ := (1 + p) / 2

end ActuarialAssurances.Fractional


