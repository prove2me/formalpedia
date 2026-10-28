-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
-- name    : TaoFivePrimes_RHExtendedMomentCachedNumerator
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:12:14.018766+00:00
-- url     : https://prove2.me/theorems/4066aee9-e3c0-42ca-99f7-4e5cf1baafeb
-- title:
--   Cached common-denominator Mellin rule
-- statement:
--   For each nonnegative moment index $j$, this definition forms a rational value $3\widetilde N_j/D_j$ from the cached theta-jet correlations, factorials, and binomial coefficients.
--
--   $$
--   \widetilde Q_j=\frac{3\widetilde N_j}{D_j}.
--   $$
--
--   This definition supports efficient exact evaluation. It does not itself assert that the cached data agree with the original quadrature.
-- source:
--   Derived here from the exact theta-jet and Mellin quadrature framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham.

/- Cached integer numerator for the Mellin quadrature rule. The underlying
theta-jet data are due to sometik179, with theta/Mellin foundations by
Gabewhigham. Equality with the uncached numerator is a separate theorem. -/
import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelationCache
set_option autoImplicit false
open Finset

namespace RHNextMomentCached

noncomputable def panelNumerator (i k : ℕ) : ℤ :=
  ∑ m ∈ range (k+1), if m<184 then
    TaoFivePrimes_RHExtendedMomentCorrelationCache i m*(12:ℤ)^m*
      ((12*(2*i+1):ℕ):ℤ)^(k-m)*(RHNextMomentInteger.fastChoose k m:ℤ) else 0

noncomputable def numerator (j : ℕ) : ℤ :=
  ∑ i ∈ range 16, panelNumerator i (2*j)

end RHNextMomentCached

noncomputable def TaoFivePrimes_RHExtendedMomentCachedRule (j : ℕ) : ℚ :=
  3*(RHNextMomentCached.numerator j:ℚ)/(RHNextMomentInteger.denominator j:ℚ)


