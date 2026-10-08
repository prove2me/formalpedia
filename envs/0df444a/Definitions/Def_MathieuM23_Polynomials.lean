-- Prove2me | Definitions.Def_MathieuM23_Polynomials
-- name    : MathieuM23_Polynomials
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T15:05:06.076985+00:00
-- url     : https://prove2.me/theorems/30d862c5-2694-4528-85e8-3b5ab7145abe
-- title:
--   The degree-23 polynomials of Examples 1.2 and 3.7
-- statement:
--   Two explicit monic polynomials of degree 23 with integer coefficients, regarded in $\mathbb{Q}[x]$:
--
--   1. $f_{1.2}(x)=x^{23}-184x^{21}-1150x^{20}+26151x^{19}+18400x^{18}-1808490x^{17}+1545462x^{16}+67672923x^{15}-42732528x^{14}-1333395744x^{13}+290615166x^{12}+10550424369x^{11}+3700476348x^{10}+35123826654x^{9}-194398310718x^{8}-1023887308293x^{7}+3961650395556x^{6}+1949980486716x^{5}-28142323927002x^{4}+53599151839311x^{3}-46185312415788x^{2}+19169943578802x-3150159884154$ (Example 1.2);
--   2. $f_{3.7}(x)=x^{23}+46x^{21}-598x^{20}+1679x^{19}-21620x^{18}+127420x^{17}-361974x^{16}+2223732x^{15}-9392096x^{14}+17344116x^{13}-71999476x^{12}+320807726x^{11}-436105484x^{10}+83587888x^{9}-2463757240x^{8}+9451874955x^{7}-5728074376x^{6}-26037806834x^{5}+63691532334x^{4}-67357061907x^{3}+38754121124x^{2}-11217790920x+1243077066$ (Example 3.7).
--
--   The source states that the splitting field of each is an $M_{23}$-extension of $\mathbb{Q}$.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 1, Example 1.2 and p. 7, Example 3.7

import Mathlib

/-! # The explicit degree-23 polynomials of Example 1.2 and Example 3.7 -/

namespace MathieuM23

open Polynomial

/-- The polynomial `f(x)` of Example 1.2. -/
noncomputable def fEx12 : ℚ[X] :=
  X ^ 23 - 184 * X ^ 21 - 1150 * X ^ 20 + 26151 * X ^ 19 + 18400 * X ^ 18 - 1808490 * X ^ 17
    + 1545462 * X ^ 16 + 67672923 * X ^ 15 - 42732528 * X ^ 14 - 1333395744 * X ^ 13
    + 290615166 * X ^ 12 + 10550424369 * X ^ 11 + 3700476348 * X ^ 10 + 35123826654 * X ^ 9
    - 194398310718 * X ^ 8 - 1023887308293 * X ^ 7 + 3961650395556 * X ^ 6
    + 1949980486716 * X ^ 5 - 28142323927002 * X ^ 4 + 53599151839311 * X ^ 3
    - 46185312415788 * X ^ 2 + 19169943578802 * X - 3150159884154

/-- The polynomial `f(x)` of Example 3.7. -/
noncomputable def fEx37 : ℚ[X] :=
  X ^ 23 + 46 * X ^ 21 - 598 * X ^ 20 + 1679 * X ^ 19 - 21620 * X ^ 18 + 127420 * X ^ 17
    - 361974 * X ^ 16 + 2223732 * X ^ 15 - 9392096 * X ^ 14 + 17344116 * X ^ 13
    - 71999476 * X ^ 12 + 320807726 * X ^ 11 - 436105484 * X ^ 10 + 83587888 * X ^ 9
    - 2463757240 * X ^ 8 + 9451874955 * X ^ 7 - 5728074376 * X ^ 6 - 26037806834 * X ^ 5
    + 63691532334 * X ^ 4 - 67357061907 * X ^ 3 + 38754121124 * X ^ 2
    - 11217790920 * X + 1243077066

end MathieuM23


