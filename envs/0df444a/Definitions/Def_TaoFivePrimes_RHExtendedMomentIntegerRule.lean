-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
-- name    : TaoFivePrimes_RHExtendedMomentIntegerRule
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:00:52.808364+00:00
-- url     : https://prove2.me/theorems/9f116596-d438-49d9-ac8a-e423c6faa8fd
-- title:
--   Common-denominator integer Mellin moment rule
-- statement:
--   For each nonnegative integer $j$, this definition gives a rational value $3N_j/D_j$, where $N_j$ is a finite integer sum of theta-jet correlations and binomial coefficients, and $D_j$ is a positive common denominator involving $(2j)!$.
--
--   $$
--   Q_j^{\mathrm{int}}=\frac{3N_j}{D_j}.
--   $$
--
--   The common-denominator form is suitable for exact integer certificates. The definition alone asserts no equality with another rule, numerical enclosure, or zeta zero-location statement.
-- source:
--   Common-denominator reorganization of the published 16-panel theta/Mellin certificate of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The factorial denominator is allowed to vary with the moment order.

/- Common-denominator integer form of the rational Mellin quadrature rule.
The underlying theta-jet data are from sometik179's certificate, with
theta/Mellin foundations by Gabewhigham. The definitions alone assert no
identity, numerical enclosure, or zero-location result. -/
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
open Finset

namespace RHNextMomentInteger

noncomputable def weightDenominator : ℕ :=
  RH14MomentEnclosureProof.CertifiedMomentWeights.denominator

noncomputable def weight (j : ℕ) : ℕ :=
  RH14MomentEnclosureProof.CertifiedMomentWeights.weight j

noncomputable def correlation (i m : ℕ) : ℤ :=
  ∑ l ∈ range (184-m), (RHNextMomentRule.centers i).getD l 0 * (weight (m+l):ℤ)

noncomputable def fastChoose (k m : ℕ) : ℕ :=
  if m≤k then k.factorial/(m.factorial*(k-m).factorial) else 0

noncomputable def panelNumerator (i k : ℕ) : ℤ :=
  ∑ m ∈ range (k+1), if m<184 then
    correlation i m*(12:ℤ)^m*((12*(2*i+1):ℕ):ℤ)^(k-m)*(fastChoose k m:ℤ) else 0

noncomputable def numerator (j : ℕ) : ℤ :=
  ∑ i ∈ range 16, panelNumerator i (2*j)

noncomputable def denominator (j : ℕ) : ℕ :=
  16*CertifiedFixedPoint.scale310*weightDenominator*(2*j).factorial

end RHNextMomentInteger

noncomputable def TaoFivePrimes_RHExtendedMomentIntegerRule (j : ℕ) : ℚ :=
  3*(RHNextMomentInteger.numerator j:ℚ)/(RHNextMomentInteger.denominator j:ℚ)


