-- Prove2me | Definitions.Def_IAFTRL_chi
-- name    : IAFTRL_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:53.563701+00:00
-- url     : https://prove2.me/theorems/94e9cec3-ac55-4c48-b1e0-d87786a416fc
-- title:
--   Proxy function $\chi(x)=e^x+e^{-x}-2$
-- statement:
--   The **proxy function** is
--   $$
--   \chi(x)=e^x+e^{-x}-2=4\sinh^2(x/2).
--   $$
--   It is even, convex, nonnegative and increasing in $|x|$ (Lemma J.4), and it is used in the stability constraint (2.3f).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17; Lemma J.4, p.206

import Mathlib

namespace IAFTRL

/-- **The proxy function `χ`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17: "`χ(x) = e^x + e^{−x} − 2`"; Lemma J.4,
p.206.

`chi x = e^x + e^{−x} − 2`. -/
noncomputable def chi (x : ℝ) : ℝ :=
  Real.exp x + Real.exp (-x) - 2

end IAFTRL


