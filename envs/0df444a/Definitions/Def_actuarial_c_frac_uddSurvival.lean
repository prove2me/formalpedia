-- Prove2me | Definitions.Def_actuarial_c_frac_uddSurvival
-- name    : actuarial_c_frac_uddSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:16:15.847017+00:00
-- url     : https://prove2.me/theorems/d11a6091-6bc7-4c8d-8bf5-f3152fd6af42
-- title:
--   UDD linear conditional survival at fraction u of a policy year.
-- statement:
--   UDD linear conditional survival at fraction u of a policy year.
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

noncomputable def uddSurvival (p u : ℝ) : ℝ :=
  1 - (1 - p) * u

end ActuarialAssurances.Fractional


