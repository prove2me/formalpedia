-- Prove2me | Definitions.Def_WeightedCongestionBR_RatData
-- name    : WeightedCongestionBR_RatData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:07.385916+00:00
-- url     : https://prove2.me/theorems/a188347c-29ed-434b-bc95-55596c98987c
-- title:
--   Rational data of a game
-- statement:
--   The rational description of a weighted polynomial congestion game of degree $d$: rational weights $w_u$ for the players and rational coefficients $a_{e,\nu}$, $\nu=0,\dots,d$, for the costs $c_e(x)=\sum_{\nu=0}^d a_{e,\nu}x^\nu$. Theorem 4 measures running time against the bit size of this description.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- Rational data of a polynomial weighted congestion game of degree `d` (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18,
"the number of bits of the representation of its input game"): rational weights `w_u` and rational
coefficients `a_{e,ν}`, `ν = 0, …, d`, of the costs `c_e(x) = ∑_ν a_{e,ν} x^ν`.

**Formalization Note** `IsRatInstance` ties the data to a game. -/
structure RatData (n r d : ℕ) where
  /-- The weights `w_u`. -/
  w : Fin n → ℚ
  /-- The coefficients `a_{e,ν}`. -/
  a : Fin r → Fin (d + 1) → ℚ

end WeightedCongestionBR


