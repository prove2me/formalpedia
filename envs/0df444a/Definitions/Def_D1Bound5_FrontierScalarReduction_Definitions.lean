-- Prove2me | Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
-- name    : D1Bound5_FrontierScalarReduction_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:55:33.850628+00:00
-- url     : https://prove2.me/theorems/4a41d5de-3cf4-46b6-a716-cd1fc8ba2a1e
-- title:
--   Frontier Scalar Reduction
-- statement:
--   Definitions for frontier scalar reduction in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `frontierK`, `frontierL`, `frontierQ`, `frontierP`, `frontierJ`.
-- source:
--   D1Bound5/FrontierScalarReduction.lean, lines 10-11, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528; D1Bound5/FrontierScalarReduction.lean, lines 12-12, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528; D1Bound5/FrontierScalarReduction.lean, lines 13-14, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528; D1Bound5/FrontierScalarReduction.lean, lines 15-15, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528; D1Bound5/FrontierScalarReduction.lean, lines 16-19, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

noncomputable def frontierK (alpha beta : ℝ) : ℝ :=
  (1/2+1/(7*alpha*beta))^2*(1/2+1/(7*beta^2))
noncomputable def frontierL (alpha beta : ℝ) : ℝ := 6*frontierK alpha beta-1/2
noncomputable def frontierQ (alpha beta : ℝ) : ℝ :=
  9*(1/2+1/(7*alpha*beta))^2*(1/2+1/(7*beta^2))^2
noncomputable def frontierP (alpha beta : ℝ) : ℝ := 2/(alpha*beta)+1/beta^2
noncomputable def frontierJ (alpha beta : ℝ) : ℝ :=
  2*frontierK alpha beta*(2/(alpha^2*beta^2)+1/beta^4)+
  frontierL alpha beta*(1/(alpha^2*beta^2)+2/(alpha*beta^3))+
  frontierQ alpha beta/(alpha^2*beta^4)





end D1Bound5
end


