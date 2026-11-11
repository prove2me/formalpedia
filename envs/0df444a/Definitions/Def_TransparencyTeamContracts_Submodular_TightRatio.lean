-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_TightRatio
-- name    : TransparencyTeamContracts_Submodular_TightRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:30:49.769505+00:00
-- url     : https://prove2.me/theorems/9971437d-00dd-47b8-9126-57168d10b165
-- title:
--   Exact additive transparency lower-bound ratio
-- statement:
--   For the even sizes $n\ge2$ in Proposition 4.3, define
--   $$R(n)=\frac{4(3n^3+n-1)}{3n^2(3n+2)}.$$
--   The rational expression is evaluated over the reals, after casting $n$, so no natural-number subtraction occurs. All theorem uses have a strictly positive denominator. The formula is also a total auxiliary function at other natural numbers; no contract-instance claim is made there. It records the exact ratio in the additive construction and its limit along the positive even integers.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Proposition 4.3, printed pp.16–17 (PDF pp.18–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib

namespace TransparencyTeamContracts.Submodular

/-- Proposition 4.3, printed p.16 (PDF 18). Intended domain: even n ≥ 2.
All arithmetic is real, so no natural subtraction or division occurs. -/
noncomputable def tightRatio (n : ℕ) : ℝ :=
  4 * (3 * (n : ℝ) ^ 3 + (n : ℝ) - 1) /
    (3 * (n : ℝ) ^ 2 * (3 * (n : ℝ) + 2))

end TransparencyTeamContracts.Submodular


