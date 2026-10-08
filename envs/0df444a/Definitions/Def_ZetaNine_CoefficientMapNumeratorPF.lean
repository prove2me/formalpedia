-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapNumeratorPF
-- name    : ZetaNine_CoefficientMapNumeratorPF
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-07T08:05:42.443763+00:00
-- url     : https://prove2.me/theorems/af79e524-3415-428a-8f8f-7367a36c73a4
-- title:
--   Actual numerator jets and polynomial reconstruction
-- statement:
--   Let $m$ be a nonnegative integer, and write
--   $$
--   D_m(z)=\prod_{k=0}^{m}(z+k),\qquad
--   C_{m,j}(z)=\prod_{\substack{0\le k\le m\\k\ne j}}(z+k).
--   $$
--   For $0\le j\le m$ and $1\le s\le9$, define the rational coefficient
--   $$
--   c_{m,j,s}(A)=[X^{9-s}]\,
--   \frac{A(X-j)}{C_{m,j}(X-j)^9}
--   $$
--   using the formal power series at $X=0$. The denominator has nonzero constant coefficient, so this formal inverse is defined.
--
--   For a rational polynomial $A$, let $T_{m,j}(A)$ be the truncation to degrees below nine of this formal series. This module defines the series, its coefficients, the corresponding local polynomial block, and the finite reconstruction
--   $$
--   P_m(A)(z)=\sum_{j=0}^{m}\sum_{s=1}^{9}
--   c_{m,j,s}(A)\,C_{m,j}(z)^9(z+j)^{9-s}.
--   $$
--   These definitions let subsequent theorems compare an arbitrary proper numerator with its actual local coefficients. The module contains five definitions; it does not assume a partial-fraction identity.
-- source:
--   Original zeta9 research, 2026-10-04: research/coefficient-map-numerator-pf-native-2026-10-04.md; formalization/CoefficientMapNumeratorPartialFractions.lean, complete SOURCE SHA256 2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77. Actual pure definitions: formalization/CoefficientMapFormalTransportData.lean (numeratorClearedSeries, numeratorLocalCoefficient); formalization/CoefficientMapNumeratorPartialFractions.lean (numeratorLocalTruncation, numeratorPartialBlock, numeratorPartialNumerator).

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_CoefficientMap
import Definitions.Def_ZetaNine_CoefficientMapJet
import Definitions.Def_ZetaNine_CoefficientMapInjectivity
import Definitions.Def_ZetaNine_CoefficientMapPartialFractions
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic





set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportData

open CoefficientMapJet CoefficientMapInjectivity















/-- Genuine formal jet for an arbitrary numerator, not an abstract array. -/
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹

def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (numeratorClearedSeries m j A)









/- Planned universal theorem, NOT YET PROVED OR COMPILED:

weightedLocalCoefficient (n+2) j s (X^r.val) =
  extendedOldCoefficient n j s (connectionP n r) +
  extendedRemainderCoefficient n j s (connectionQ n r) -
  previousRemainderCoefficient n j s (connectionQ n r)

for n>=1, j<=n+2 and 1<=s<=9.  From this derive all nine rho
relations and the rational constant correction, then the actual row matrix
identity F_(n+2) = connectionGamma n * F_n for Even n>=2.
-/

end ZetaNine.CoefficientMapFormalTransportData





set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapNumeratorPartialFractions

open CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData

def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (numeratorClearedSeries m j A)

def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial m j ^ 9 *
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ))

def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (numeratorLocalCoefficient m j s A) *
      clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

















































end ZetaNine.CoefficientMapNumeratorPartialFractions


