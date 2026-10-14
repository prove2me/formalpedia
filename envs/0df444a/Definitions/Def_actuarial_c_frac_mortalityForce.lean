-- Prove2me | Definitions.Def_actuarial_c_frac_mortalityForce
-- name    : actuarial_c_frac_mortalityForce
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T20:16:33.250084+00:00
-- url     : https://prove2.me/theorems/b75a1737-a210-43f1-befb-9c2b704c4802
-- title:
--   Finite nonnegative constant mortality force -log(p) for 0<p≤1.
-- statement:
--   Finite nonnegative constant mortality force -log(p) for 0<p≤1.
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

noncomputable def mortalityForce (p : ℝ) : ℝ := -Real.log p

end ActuarialAssurances.Fractional


