-- Prove2me | Definitions.Def_DetDLP_D1Radius
-- name    : DetDLP_D1Radius
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:29:13.9088+00:00
-- url     : https://prove2.me/theorems/12a29ed8-7f58-4f48-8e25-1c521bb87acb
-- title:
--   Exact integer scan for the Appendix D radius
-- statement:
--   The radius is the floored logarithm of the scale divided by the rounded maximum degree cutoff, bounded below by one. The integer scan counts eligible exponents up to the binary length of the scale. The capped exponent in the test ensures polynomial input size even when the test is called outside the scan.

import Definitions.Def_DetDLP_OpenAIAppendixD

set_option autoImplicit false
namespace DetDLP.D1

def radiusTest (b deg j : ℕ) : Bool := decide (deg ≤ b / 2^j ∧ b^9 ≤ (b / 2^j)^10)

noncomputable def radius (b deg : ℕ) : ℕ :=
  max 1 ⌊Real.logb 2 ((b:ℝ) / (max deg ⌈(b:ℝ)^((9:ℝ)/10)⌉₊ : ℕ))⌋₊


def scanTest (b deg j : ℕ) :=
  let t := min j b.bits.length
  decide (j = 1) || (decide (2 ≤ j) && (decide (deg ≤ b / 2^t) && decide (b^9 ≤ (b / 2^t)^10)))

def radiusScan (p : ℕ × ℕ) := ((List.range (p.1.bits.length+1)).filter (scanTest p.1 p.2)).length


end DetDLP.D1


