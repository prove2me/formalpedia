-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirect132Integer
-- name    : TaoFivePrimes_RHDirect132Integer
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:59:38.962111+00:00
-- url     : https://prove2.me/theorems/2605d7ae-b49f-441b-b46b-cb5b45f0dd83
-- title:
--   Integer phase convolution of the theta correlations
-- statement:
--   Given cached integer theta correlations $B_{i,r}$ and proposed phase factors $F_\ell$, define the Gaussian-integer convolution
--
--   $$
--   \Gamma_{i,m}=\sum_{\ell=0}^{183-m} B_{i,m+\ell}F_\ell i^\ell.
--   $$
--
--   The real and imaginary components are finite integer sums. Their relation to the analytic rule and any cached numerical evaluations require separate certificates.
-- source:
--   Exact phase convolution built on the published theta-jet correlation data of sometik179, with theta/Mellin foundations due to Gabewhigham.

/- Candidate integer phase correlations formed from previously published
theta correlations. The data alone assert no equality or error bound. -/
import Definitions.Def_TaoFivePrimes_RHDirect132PhaseFactors
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelationCache
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
set_option maxRecDepth 100000
open Finset

namespace RHDirect132Integer

def phaseFactor (l : ℕ) : ℤ := (TaoFivePrimes_RHDirect132PhaseFactors.getD l 0:ℤ)
def realSign (l : ℕ) : ℤ := if l%4=0 then 1 else if l%4=2 then -1 else 0
def imagSign (l : ℕ) : ℤ := if l%4=1 then 1 else if l%4=3 then -1 else 0

noncomputable def gammaRe (i m : ℕ) : ℤ :=
  ∑ l ∈ range (184-m), TaoFivePrimes_RHExtendedMomentCorrelationCache i (m+l)*
    phaseFactor l*realSign l

noncomputable def gammaIm (i m : ℕ) : ℤ :=
  ∑ l ∈ range (184-m), TaoFivePrimes_RHExtendedMomentCorrelationCache i (m+l)*
    phaseFactor l*imagSign l

end RHDirect132Integer


