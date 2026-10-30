-- Prove2me | Definitions.Def_JailletLu_g
-- name    : JailletLu_g
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:47.529907+00:00
-- url     : https://prove2.me/theorems/8a8361b4-5566-4b2e-bd5c-4a6160e23da0
-- title:
--   The function $g(y,x)=h(y,0)-h(y,x)$
-- statement:
--   For real $y,x$,
--   $$
--   g(y,x)=h(y,0)-h(y,x).
--   $$
--   By Claim 2, $g(f_{a_1},m_{a_1,a})$ is the probability of the event $E_{a_1,a}$ that a list $\langle a_1,a\rangle$ arrives after $a_1$ is full.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 2, p. 14

import Mathlib
import Definitions.Def_JailletLu_h

namespace JailletLu

/-- **The function `g(y, x) = h(y, 0) − h(y, x)` of Claim 2.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 2, p. 14: "g(y, x) = h(y, 0) − h(y, x)". -/
noncomputable def g (y x : ℝ) : ℝ :=
  h y 0 - h y x

end JailletLu


