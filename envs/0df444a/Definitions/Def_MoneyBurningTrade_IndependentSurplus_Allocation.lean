-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Allocation
-- name    : MoneyBurningTrade_IndependentSurplus_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:19.874141+00:00
-- url     : https://prove2.me/theorems/225bcbe7-a085-44c5-82b5-4e661bf68c99
-- title:
--   Equation (18) — normalized grid allocation
-- statement:
--   Given grid rounding indices and growth factor $\Gamma$, define
--
--   $$x(s,b)=\begin{cases}0&\iota_S(s)\ge\iota_B(b),\\\Gamma^{\iota_B(b)-\iota_S(s)-1}/\Gamma^{n-1}&\iota_S(s)<\iota_B(b).\end{cases}$$
--
--   The numerator uses integer exponents, preserving every sign. On the positive branch its exponent lies between zero and $n-1$. Normalization to allocation probabilities and the minimum positive allocation bound are asserted by Lemma 4.3, rather than assumed in this definition.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.3, equation (18), printed p. 24 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Thresholds
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_GrowthFactor

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Equation (18), using signed integer exponents. On the positive branch
the numerator exponent is between 0 and n-1; the denominator exponent n-1
is nonnegative. There is no truncated negative exponent. -/
noncomputable def gridAllocation (G : Grid) (τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if sellerIndex G τ p.1 < buyerIndex G τ p.2 then
    growthFactor G τ ^ ((buyerIndex G τ p.2 : ℤ) - (sellerIndex G τ p.1 : ℤ) - 1) /
      growthFactor G τ ^ (G.n - 1)
  else 0

end MoneyBurningTrade.IndependentSurplus


