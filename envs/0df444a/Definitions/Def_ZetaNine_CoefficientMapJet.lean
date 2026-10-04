-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapJet
-- name    : ZetaNine_CoefficientMapJet
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:52:17.736537+00:00
-- url     : https://prove2.me/theorems/b49898b0-a988-42c3-9ddb-8e3e25f22ca8
-- title:
--   Actual shifted products and formal local coefficient series
-- statement:
--   Let $n,j$ be natural numbers and let $z$ be a formal variable. Set $T_j(z)=z-j$ and define the actual shifted numerator and cleared denominator by
--
--   $$N_{n,j}(z)=n!^7\prod_{i=1}^{n}(T_j(z)-i)\prod_{i=1}^{n}(T_j(z)+n+i),\qquad D_{n,j}(z)=\prod_{0\le k\le n,\ k\ne j}(T_j(z)+k).$$
--
--   Set $U_{n,j}(z)=T_j(z)(T_j(z)+n)$. In $\mathbb Q[[z]]$, define $S_{n,j}=N_{n,j}(D_{n,j}^{9})^{-1}$ and, for any $W\in\mathbb Q[X]$, $S^W_{n,j}=S_{n,j}W(U_{n,j})$. For natural $s$, define $c_{n,j,s}=[z^{9-s}]S_{n,j}$ and $c^W_{n,j,s}=[z^{9-s}]S^W_{n,j}$ using natural-number subtraction; the pole-order interpretation is restricted to $1\le s\le9$ and $j\le n$. Also define the integer polynomial $U^{\mathbb Z}_{n,j}=-j(n-j)+(n-2j)X+X^2$, where $n-j$ is natural subtraction.
--
--   These nine constructions use genuine shifted finite products and formal power-series coefficients. They provide the interface for uniqueness and polynomial-multiplier convolution. Formal inversion here is a ring construction, with its nonzero-constant justification proved in the Solution modules. It does not assert numerical evaluation or convergence of an infinite series.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-jet-2026-10-03.md (actual shifted numerator, cleared denominator, formal local quotient and all nine convolution orders); underlying missions/zeta9/round5/research/arithmetic.md, equation (5), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMapJet.lean, SHA256 e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a; frozen actual Base source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. The nine definition declarations retain their exact original Lean parser spans.

import Definitions.Def_ZetaNine_CoefficientMap
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet

def shiftedVariable (j : ℕ) : ℚ[X] := X - C (j : ℚ)

def shiftedNumerator (n j : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (shiftedVariable j - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (shiftedVariable j + C (n : ℚ) + C ((i : ℚ) + 1)))

def shiftedClearedDenominator (n j : ℕ) : ℚ[X] :=
  ∏ k ∈ (range (n + 1)).erase j, (shiftedVariable j + C (k : ℚ))

def localU (n j : ℕ) : ℚ[X] := shiftedVariable j * (shiftedVariable j + C (n : ℚ))

def integerLocalU (n j : ℕ) : ℤ[X] :=
  C (-(j : ℤ) * (n - j : ℕ)) + C ((n : ℤ) - 2 * j) * X + X ^ 2

def clearedSeries (n j : ℕ) : PowerSeries ℚ :=
  (shiftedNumerator n j : PowerSeries ℚ) *
    ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹

def weightedClearedSeries (n j : ℕ) (W : ℚ[X]) : PowerSeries ℚ :=
  clearedSeries n j * (W.comp (localU n j) : PowerSeries ℚ)

def localCoefficient (n j s : ℕ) : ℚ := PowerSeries.coeff (9 - s) (clearedSeries n j)

def weightedLocalCoefficient (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (weightedClearedSeries n j W)

end ZetaNine.CoefficientMapJet


