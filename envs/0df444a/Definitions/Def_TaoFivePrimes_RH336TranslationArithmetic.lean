-- Prove2me | Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
-- name    : TaoFivePrimes_RH336TranslationArithmetic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:09:10.311444+00:00
-- url     : https://prove2.me/theorems/105c2f0e-ce09-4235-9aa1-6088be86dc88
-- title:
--   Exact integer translation of 320 Mellin moment candidates
-- statement:
--   This module defines a common denominator, integer moment numerators, and an exact binomial translation numerator for 336 candidate Mellin moments. The published title and source comment mistakenly say 320; the definition itself sums 336 candidates. It is arithmetic data, and the xi approximation is separate.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

/- Exact integer translation of 320 proposed Mellin moments. The original
moment data and xi translation framework are due to sometik179, with
theta/Mellin foundations by Gabewhigham. This definition is arithmetic data. -/
import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData320to335
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
open Finset

namespace RH336TranslationArithmetic

noncomputable def denominator : ℕ := 8*10^64*2^5376

noncomputable def momentInteger (j : ℕ) : ℤ :=
  if j<320 then RH320TranslationArithmetic.momentInteger j
  else TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0

noncomputable def chooseFast (k n : ℕ) : ℕ :=
  if n≤k then k.factorial/(n.factorial*(k-n).factorial) else 0

noncomputable def numerator (p : ℤ) (S n : ℕ) : ℤ :=
  (if n=0 then (4*10^64*2^5376:ℤ) else 0)*(S:ℤ)-
  (S:ℤ)*∑ j ∈ range 336,
    momentInteger j*(-1:ℤ)^j*((2^(5376-16*j+n):ℕ):ℤ)*
    ((chooseFast (2*j+2) n:ℤ)*p^(2*j+2-n)+
      (chooseFast (2*j) n:ℤ)*p^(2*j-n))

end RH336TranslationArithmetic


