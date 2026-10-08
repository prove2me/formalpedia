-- Prove2me | Definitions.Def_MazurHuang_NineteenTatePolynomial
-- name    : MazurHuang_NineteenTatePolynomial
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T14:54:59.982179+00:00
-- url     : https://prove2.me/theorems/12d4fa8c-4737-4bbe-8d30-14e0eee4279e
-- title:
--   The order-nineteen Tate division factor
-- statement:
--   The polynomial F₁₉(b,c) is the Tate-normal-form order-nineteen division factor −ψ₁₉(0,0)/b¹²⁰.
-- source:
--   https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/TateNFDivision.lean#L139

/-
The order-nineteen Tate division factor
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib


-- Source FLT/Assumptions/MazurProof/TateNFDivision.lean:20-22; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]
/-- `-ψ₁₉(0,0) / b¹²⁰`.  80 monomials, total degree 15–24. -/
def F19 (b c : K) : K :=
    b ^ 15
      - 10 * b ^ 14 * c
      - 20 * b ^ 13 * c ^ 3
      + 45 * b ^ 13 * c ^ 2
      + 69 * b ^ 12 * c ^ 5
      + 195 * b ^ 12 * c ^ 4
      - 120 * b ^ 12 * c ^ 3
      - 121 * b ^ 11 * c ^ 7
      - 588 * b ^ 11 * c ^ 6
      - 861 * b ^ 11 * c ^ 5
      + 210 * b ^ 11 * c ^ 4
      + 105 * b ^ 10 * c ^ 9
      + 870 * b ^ 10 * c ^ 8
      + 2235 * b ^ 10 * c ^ 7
      + 2275 * b ^ 10 * c ^ 6
      - 252 * b ^ 10 * c ^ 5
      - 48 * b ^ 9 * c ^ 11
      - 585 * b ^ 9 * c ^ 10
      - 2720 * b ^ 9 * c ^ 9
      - 4995 * b ^ 9 * c ^ 8
      - 4005 * b ^ 9 * c ^ 7
      + 210 * b ^ 9 * c ^ 6
      + 11 * b ^ 8 * c ^ 13
      + 183 * b ^ 8 * c ^ 12
      + 1320 * b ^ 8 * c ^ 11
      + 4851 * b ^ 8 * c ^ 10
      + 7290 * b ^ 8 * c ^ 9
      + 4950 * b ^ 8 * c ^ 8
      - 120 * b ^ 8 * c ^ 7
      - b ^ 7 * c ^ 15
      - 21 * b ^ 7 * c ^ 14
      - 231 * b ^ 7 * c ^ 13
      - 1531 * b ^ 7 * c ^ 12
      - 5466 * b ^ 7 * c ^ 11
      - 7308 * b ^ 7 * c ^ 10
      - 4410 * b ^ 7 * c ^ 9
      + 45 * b ^ 7 * c ^ 8
      + 120 * b ^ 6 * c ^ 14
      + 990 * b ^ 6 * c ^ 13
      + 4117 * b ^ 6 * c ^ 12
      + 5166 * b ^ 6 * c ^ 11
      + 2862 * b ^ 6 * c ^ 10
      - 10 * b ^ 6 * c ^ 9
      - 34 * b ^ 5 * c ^ 16
      - 165 * b ^ 5 * c ^ 15
      - 465 * b ^ 5 * c ^ 14
      - 2190 * b ^ 5 * c ^ 13
      - 2610 * b ^ 5 * c ^ 12
      - 1350 * b ^ 5 * c ^ 11
      + b ^ 5 * c ^ 10
      + 25 * b ^ 4 * c ^ 18
      + 150 * b ^ 4 * c ^ 17
      + 363 * b ^ 4 * c ^ 16
      + 320 * b ^ 4 * c ^ 15
      + 885 * b ^ 4 * c ^ 14
      + 945 * b ^ 4 * c ^ 13
      + 455 * b ^ 4 * c ^ 12
      - 6 * b ^ 3 * c ^ 20
      - 45 * b ^ 3 * c ^ 19
      - 161 * b ^ 3 * c ^ 18
      - 333 * b ^ 3 * c ^ 17
      - 225 * b ^ 3 * c ^ 16
      - 281 * b ^ 3 * c ^ 15
      - 240 * b ^ 3 * c ^ 14
      - 105 * b ^ 3 * c ^ 13
      + b ^ 2 * c ^ 22
      + 6 * b ^ 2 * c ^ 21
      + 21 * b ^ 2 * c ^ 20
      + 56 * b ^ 2 * c ^ 19
      + 126 * b ^ 2 * c ^ 18
      + 81 * b ^ 2 * c ^ 17
      + 61 * b ^ 2 * c ^ 16
      + 39 * b ^ 2 * c ^ 15
      + 15 * b ^ 2 * c ^ 14
      - 15 * b * c ^ 19
      - 10 * b * c ^ 18
      - 6 * b * c ^ 17
      - 3 * b * c ^ 16
      - b * c ^ 15
      - c ^ 21


end MazurProof.TateNFDivision
end


