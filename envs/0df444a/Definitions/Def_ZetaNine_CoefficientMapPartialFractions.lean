-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapPartialFractions
-- name    : ZetaNine_CoefficientMapPartialFractions
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T17:54:58.281163+00:00
-- url     : https://prove2.me/theorems/7735a339-5a83-4d33-8bda-12daefbcd63a
-- title:
--   Actual finite partial-fraction numerator and local candidate series
-- statement:
--   For natural $n,j$ and $W\in\mathbb Q[X]$, let $D^*_{n,j}(t)=\prod_{0\le k\le n,\ k\ne j}(t+k)$ and let $S^W_{n,j}$ be the actual weighted local formal quotient imported from the genuine shifted products. Set $T_{n,j}^W=\operatorname{trunc}_{<9}S^W_{n,j}$ and $B_{n,j}^W=(D^*_{n,j})^9T^W_{n,j}(X+j)$. Using the actual coefficients $c^W_{n,j,s}=[z^{9-s}]S^W_{n,j}$, define
--
--   $$P_n^W=\sum_{j=0}^{n}\sum_{s=1}^{9}c^W_{n,j,s}(D^*_{n,j})^9(X+j)^{9-s}.$$
--
--   Define the candidate cleared local series by $P_n^W(z-j)(D_{n,j}(z)^9)^{-1}$ in $\mathbb Q[[z]]$. These five definitions construct a candidate from the genuine local coefficients; neither a global partial-fraction conclusion nor an arbitrary coefficient array is assumed. The complete identity with the actual weighted numerator is a subsequent theorem on the strict proper domain.
-- source:
--   Zeta(9) actual finite global partial-fraction research: missions/zeta9/research/coefficient-map-partial-fractions-2026-10-03.md. Frozen Lean source missions/zeta9/formalization/CoefficientMapPartialFractions.lean, SHA256 eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a. The original actual Base/Jet/Injectivity finite products and local formal coefficients are used throughout.

import Definitions.Def_ZetaNine_CoefficientMapInjectivity
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

def clearedPolePolynomial (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ))

def localTruncation (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (CoefficientMapJet.weightedClearedSeries n j W)

def partialBlock (n j : ℕ) (W : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (localTruncation n j W).comp (X + C (j : ℚ))

def partialNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    C (CoefficientMapJet.weightedLocalCoefficient n j s W) *
      clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

def candidateClearedSeries (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  ((partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹

end ZetaNine.CoefficientMapPartialFractions


