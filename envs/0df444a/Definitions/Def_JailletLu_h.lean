-- Prove2me | Definitions.Def_JailletLu_h
-- name    : JailletLu_h
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:17.099297+00:00
-- url     : https://prove2.me/theorems/83365b5b-860d-4252-a163-523c6515b44d
-- title:
--   The function $h(y,x)$ of Claim 2
-- statement:
--   For real $y,x$,
--   $$
--   h(y,x)=\begin{cases}\dfrac{y}{y-x}\big(e^{-x}-e^{-y}\big),& x\ne y,\\[4pt] y\,e^{-y},& x=y.\end{cases}
--   $$
--   Claim 2 expresses the probability that advertiser $a$ is matched through a list $\langle a_1,a\rangle$ through $h$; note $h(y,0)=1-e^{-y}$ for every $y$.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 2, p. 14

import Mathlib

namespace JailletLu

/-- **The function `h(y, x)` of Claim 2.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 2, p. 14:
"h(y, x) = y/(y − x) (e^{−x} − e^{−y}) if x ≠ y; y e^{−y} if x = y".

Note `h y 0 = 1 − e^{−y}` for every `y` (both branches). -/
noncomputable def h (y x : ℝ) : ℝ :=
  if x = y then y * Real.exp (-y) else y / (y - x) * (Real.exp (-x) - Real.exp (-y))

end JailletLu


