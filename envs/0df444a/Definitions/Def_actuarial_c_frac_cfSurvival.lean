-- Prove2me | Definitions.Def_actuarial_c_frac_cfSurvival
-- name    : actuarial_c_frac_cfSurvival
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:16:24.343137+00:00
-- url     : https://prove2.me/theorems/4744ab5a-662d-4e32-b80f-01e8d99c8d1b
-- title:
--   Constant-force conditional survival at fractional time u, requiring annual survival p>0 for the actuarial interpretation.
-- statement:
--   Constant-force conditional survival at fractional time u, requiring annual survival p>0 for the actuarial interpretation.
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

noncomputable def cfSurvival (p u : ℝ) : ℝ :=
  Real.exp (Real.log p * u)

end ActuarialAssurances.Fractional


