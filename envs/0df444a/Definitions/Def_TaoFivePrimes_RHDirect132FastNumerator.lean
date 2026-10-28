-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
-- name    : TaoFivePrimes_RHDirect132FastNumerator
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:48:16.986433+00:00
-- url     : https://prove2.me/theorems/e37ca69f-21f9-4c34-aa81-1dc096042d4a
-- title:
--   Factorial-based integer numerator for height-132 rounding checks
-- statement:
--   Define a finite cached numerator using factorial quotients for the binomial coefficients, and select its real or imaginary part according to the parity of the index. For the candidate fixed-point integer $q_k$ and cached denominator $D_k$, define the two floor inequalities
--
--   $$
--   q_kD_k\le10^{90}3^{k+1}N_k<(q_k+1)D_k.
--   $$
--
--   The definition alone does not assert these inequalities or equality with another numerator.
-- source:
--   Finite theta-jet and Mellin quadrature framework by sometik179 and Gabewhigham.

/- Candidate computational form of the cached rule numerator.  Its relation
to the original cached rule and all numerical bounds are separate results. -/
import Definitions.Def_TaoFivePrimes_RHDirect132CachedRule
import Definitions.Def_TaoFivePrimes_RHDirect132FixedComponents
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open Finset

namespace RHDirect132FastNumerator

noncomputable def weight (i k m : ℕ) : ℤ :=
  (RHNextMomentInteger.fastChoose k m:ℤ)*((2*i+1:ℕ):ℤ)^(k-m)

noncomputable def panelRe (i k : ℕ) : ℤ :=
  ∑ m ∈ range (k+1), weight i k m * (RHDirect132CachedRule.gamma i m).1

noncomputable def panelIm (i k : ℕ) : ℤ :=
  ∑ m ∈ range (k+1), weight i k m * (RHDirect132CachedRule.gamma i m).2

noncomputable def numeratorRe (k : ℕ) : ℤ :=
  ∑ i ∈ range 16,
    ((RHDirect132CachedRule.phaseData.getD i (0,0)).1*panelRe i k -
      (RHDirect132CachedRule.phaseData.getD i (0,0)).2*panelIm i k)

noncomputable def numeratorIm (k : ℕ) : ℤ :=
  ∑ i ∈ range 16,
    ((RHDirect132CachedRule.phaseData.getD i (0,0)).1*panelIm i k +
      (RHDirect132CachedRule.phaseData.getD i (0,0)).2*panelRe i k)

noncomputable def component (k : ℕ) : ℤ :=
  if k%2=0 then numeratorRe k else numeratorIm k

def fixed (k : ℕ) : ℤ := TaoFivePrimes_RHDirect132FixedComponents.getD k 0

def floorHolds (k : ℕ) : Prop :=
  fixed k*(RHDirect132CachedRule.denominator k:ℤ) ≤
      (10^90:ℤ)*3^(k+1)*component k ∧
  (10^90:ℤ)*3^(k+1)*component k <
      (fixed k+1)*(RHDirect132CachedRule.denominator k:ℤ)

end RHDirect132FastNumerator


